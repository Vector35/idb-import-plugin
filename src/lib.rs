#[cfg(not(feature = "internal"))]
mod binja {
    pub use binaryninja::*;
}

#[cfg(feature = "internal")]
mod binja {
    pub use binaryninja_internal::*;
}

use binja::rc::Ref;
use binja::types::{Conf, NamedTypeReferenceClass, QualifiedName, StructureType, Type};
use binja::{
    binaryninjacore_sys::{BNMemberAccess, BNMemberScope},
    binaryview::{BinaryView, BinaryViewExt},
    command::Command,
    debuginfo::{CustomDebugInfoParser, DebugInfo, DebugInfoParser},
    interaction::get_open_filename_input,
    logger,
};
use idb_parser::{TILBucket, TILBucketType, TILOrdinal, TILSection, TILTypeInfo, Types, IDB};
use log::error;
use std::fmt::{Debug, Display, Formatter};

struct IDBParser;
struct TILParser;

#[derive(Debug)]
enum TypeError<'a> {
    FailedToParse(&'a [u8]),
}

impl<'a> Display for TypeError<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match *self {
            TypeError::FailedToParse(ref err) => write!(
                f,
                "Failed to parse type: {:?}",
                std::str::from_utf8(err).unwrap()
            ),
        }
    }
}

impl<'a> std::error::Error for TypeError<'a> {
    fn description(&self) -> &str {
        match *self {
            TypeError::FailedToParse(ref err) => std::str::from_utf8(err).unwrap(),
        }
    }
}

impl TILParser {
    fn parse_all_types<'a>(
        &'a self,
        bv: &BinaryView,
        til: &'a TILSection,
    ) -> Option<Vec<Result<(&'a [u8], binja::rc::Ref<binja::types::Type>), TypeError>>> {
        let parser = IDBParser {};
        match &til.types {
            TILBucketType::Default(default) => Some(
                default
                    .type_info
                    .iter()
                    .map(|x| {
                        if let Some(bn_type) =
                            parser.create_bn_type_from_idb(bv, &default, &x, &x.tinfo)
                        {
                            Ok((x.name.0.as_slice(), bn_type))
                        } else {
                            Err(TypeError::FailedToParse(x.name.0.as_slice()))
                        }
                    })
                    .collect(),
            ),
            TILBucketType::Zip(zip) => {
                let unzip = zip.unzip();
                Some(
                    zip.type_info
                        .iter()
                        .map(|x| {
                            if let Some(bn_type) =
                                parser.create_bn_type_from_idb(bv, &unzip, &x, &x.tinfo)
                            {
                                Ok((x.name.0.as_slice(), bn_type))
                            } else {
                                Err(TypeError::FailedToParse(x.name.0.as_slice()))
                            }
                        })
                        .collect(),
                )
            }
        }
    }
}

impl IDBParser {
    fn create_bn_type_from_idb(
        &self,
        bv: &BinaryView,
        bucket: &TILBucket,
        tinfo: &TILTypeInfo,
        ty: &Types,
    ) -> Option<Ref<Type>> {
        match ty {
            Types::Unset(mdata) => match mdata.get_base_type_flag().0 {
                0x01 => Some(Type::void()),
                0x02 => Some(Type::int(1, mdata.get_type_flag().is_signed())),
                0x03 => Some(Type::int(2, mdata.get_type_flag().is_signed())),
                0x04 => Some(Type::int(4, mdata.get_type_flag().is_signed())),
                0x05 => Some(Type::int(8, mdata.get_type_flag().is_signed())),
                0x06 => Some(Type::int(16, mdata.get_type_flag().is_signed())),
                // not too sure about this one.
                0x07 => Some(Type::int(4, mdata.get_type_flag().is_signed())),
                0x08 => Some(Type::bool()),
                0x09 => match mdata.get_type_flag().0 {
                    0x00 => Some(Type::float(4)),
                    0x10 => Some(Type::float(8)),
                    // TODO: (LONG DOUBLE) LOOK AT THIS L8R BUT THIS IS DEBATABLE SO WE ARE DOING 8
                    0x20 => Some(Type::float(8)),
                    _ => None,
                },
                _ => None,
            },
            Types::Pointer(ptr) => {
                if let Some(arch) = bv.default_arch() {
                    if let Some(ty) = self.create_bn_type_from_idb(bv, bucket, tinfo, &ptr.typ) {
                        Some(Type::pointer(&arch, &*ty))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Types::Function(fun) => {
                if let Some(return_ty) = self.create_bn_type_from_idb(bv, bucket, tinfo, &fun.ret) {
                    let mut vec = Vec::new();
                    for (t, str) in std::iter::zip(&fun.args, &tinfo.fields.0) {
                        if let Some(f) = self.create_bn_type_from_idb(bv, bucket, tinfo, &t.0) {
                            vec.push(binja::types::FunctionParameter::new(f, str.as_str(), None));
                        }
                    }

                    Some(Type::function(
                        Conf::new(&*return_ty, 100),
                        vec.as_slice(),
                        false,
                    ))
                } else {
                    None
                }
            }
            Types::Array(arr) => {
                if let Some(t) = self.create_bn_type_from_idb(bv, bucket, tinfo, &arr.elem_type) {
                    Some(Type::array(Conf::new(&*t, 100), arr.nelem as u64))
                } else {
                    None
                }
            }
            Types::Typedef(tdef) => {
                if tdef.is_ordref {
                    if let Some(lookup) = bucket
                        .type_info
                        .iter()
                        .find(|x| match x.ordinal {
                            TILOrdinal::U32(t) => {t as u64}
                            TILOrdinal::U64(t) => {t}
                        } == tdef.ordinal.0 as u64)
                    {
                        if let Some(typ) =
                            self.create_bn_type_from_idb(bv, bucket, tinfo, &lookup.tinfo)
                        {
                            Some(Type::named_type_from_type(
                                std::str::from_utf8(tinfo.name.0.as_slice()).unwrap(),
                                    &typ,
                            ))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    if bucket
                        .type_info
                        .iter()
                        .find(|x| x.name.0.as_slice() == tdef.name.as_bytes())
                        .is_some()
                    {
                        Some(Type::named_type(&binja::types::NamedTypeReference::new(
                            NamedTypeReferenceClass::UnknownNamedTypeClass,
                            "",
                            QualifiedName::from(tdef.name.as_str()),
                        )))
                    } else {
                        match tdef.name.as_str() {
                            "int8_t" => Some(Type::int(1, true)),
                            "int16_t" => Some(Type::int(2, true)),
                            "int32_t" => Some(Type::int(4, true)),
                            "int64_t" => Some(Type::int(8, true)),
                            "int128_t" => Some(Type::int(16, true)),
                            _ => {
                                error!("Failed to find typedef: {}", tdef.name.as_str());
                                None
                            }
                        }
                    }
                }
            }
            Types::Struct(str) => {
                if str.is_ref {
                    if let Some(ref_type) =
                        self.create_bn_type_from_idb(bv, bucket, tinfo, &str.ref_type.0)
                    {
                        Some(Type::named_type_from_type(
                            std::str::from_utf8(tinfo.name.0.as_slice()).unwrap(),
                            &*ref_type,
                        ))
                    } else {
                        None
                    }
                } else {
                    let mut structure = binja::types::StructureBuilder::new();
                    for (member, name) in std::iter::zip(&str.members, &tinfo.fields.0) {
                        if let Some(mem) =
                            self.create_bn_type_from_idb(bv, bucket, tinfo, &member.0)
                        {
                            structure.append(
                                mem.as_ref(),
                                name.as_str(),
                                BNMemberAccess::NoAccess,
                                BNMemberScope::NoScope,
                            );
                        }
                    }
                    let str_ref = structure.finalize();
                    Some(Type::structure(&str_ref))
                }
            }
            Types::Union(uni) => {
                if uni.is_ref {
                    if let Some(ref_type) =
                        self.create_bn_type_from_idb(bv, bucket, tinfo, &uni.ref_type.0)
                    {
                        Some(Type::named_type_from_type(
                            std::str::from_utf8(tinfo.name.0.as_slice()).unwrap(),
                            &*ref_type,
                        ))
                    } else {
                        None
                    }
                } else {
                    let mut structure = binja::types::StructureBuilder::new();
                    for (member, name) in std::iter::zip(&uni.members, &tinfo.fields.0) {
                        if let Some(mem) =
                            self.create_bn_type_from_idb(bv, bucket, tinfo, &member.0)
                        {
                            structure.append(
                                mem.as_ref(),
                                name.as_str(),
                                BNMemberAccess::NoAccess,
                                BNMemberScope::NoScope,
                            );
                        }
                    }
                    structure.set_structure_type(StructureType::UnionStructureType);
                    let str_ref = structure.finalize();
                    Some(binja::types::Type::structure(&str_ref))
                }
            }
            Types::Enum(enu) => {
                if enu.is_ref {
                    if let Some(ref_type) =
                        self.create_bn_type_from_idb(bv, bucket, tinfo, &enu.ref_type.0)
                    {
                        Some(binja::types::Type::named_type_from_type(
                            std::str::from_utf8(tinfo.name.0.as_slice()).unwrap(),
                            &*ref_type,
                        ))
                    } else {
                        None
                    }
                } else {
                    let mut eb = binja::types::EnumerationBuilder::new();
                    for (member, name) in std::iter::zip(&enu.members, &tinfo.fields.0) {
                        eb.insert(name.as_str(), member.0);
                    }
                    Some(binja::types::Type::enumeration(
                        &eb.finalize(),
                        enu.bytesize as usize,
                        Conf::new(false, 0),
                    ))
                }
            }
            Types::Bitfield(_) => {
                error!("Bitfields are not supported");
                None
            }
            Types::Unknown(_) => None,
        }
    }

    fn parse_all_types<'a>(
        &'a self,
        bv: &BinaryView,
        idb: &'a IDB,
    ) -> Option<Vec<Result<(&'a [u8], binja::rc::Ref<binja::types::Type>), TypeError>>> {
        if let Some(til) = &idb.til {
            match &til.types {
                TILBucketType::Default(default) => Some(
                    default
                        .type_info
                        .iter()
                        .map(|x| {
                            if let Some(bn_type) =
                                self.create_bn_type_from_idb(bv, &default, &x, &x.tinfo)
                            {
                                Ok((x.name.0.as_slice(), bn_type))
                            } else {
                                Err(TypeError::FailedToParse(x.name.0.as_slice()))
                            }
                        })
                        .collect(),
                ),
                TILBucketType::Zip(zip) => {
                    let unzip = zip.unzip();
                    Some(
                        zip.type_info
                            .iter()
                            .map(|x| {
                                if let Some(bn_type) =
                                    self.create_bn_type_from_idb(bv, &unzip, &x, &x.tinfo)
                                {
                                    Ok((x.name.0.as_slice(), bn_type))
                                } else {
                                    Err(TypeError::FailedToParse(x.name.0.as_slice()))
                                }
                            })
                            .collect(),
                    )
                }
            }
        } else {
            None
        }
    }

    // fn parse_type_by_name(
    //     &self,
    //     bv: &BinaryView,
    //     name: String,
    //     idb: &IDB,
    // ) -> Option<(String, binja::rc::Ref<binja::types::Type>)> {
    //     if let Some(til) = &idb.til {
    //         match &til.types {
    //             TILBucketType::Default(default) => {
    //                 if let Some(located) = default
    //                     .type_info
    //                     .iter()
    //                     .find(|ty| ty.name.clone().into_string() == name)
    //                 {
    //                     if let Some(bn_type) =
    //                         self.create_bn_type_from_idb(bv, &default, &located, &located.tinfo)
    //                     {
    //                         Some((located.name.clone().into_string(), bn_type))
    //                     } else {
    //                         None
    //                     }
    //                 } else {
    //                     None
    //                 }
    //             }
    //             TILBucketType::Zip(zip) => None,
    //             _ => None,
    //         }
    //     } else {
    //         None
    //     }
    // }
}

impl CustomDebugInfoParser for IDBParser {
    fn is_valid(&self, _view: &BinaryView) -> bool {
        true
    }

    fn parse_info(&self, debug_info: &mut DebugInfo, bv: &BinaryView) {
        if let Some(idb_file) = get_open_filename_input("Select IDB", "*.i64") {
            if let Ok(path) = idb_file.into_os_string().into_string() {
                if let Ok(idb) = IDB::parse_from_file(path) {
                    if let Some(types) = self.parse_all_types(bv, &idb) {
                        types.iter().for_each(|x| match x {
                            Ok((str, ty)) => {
                                debug_info.add_type(std::str::from_utf8(str).unwrap(), ty);
                            }
                            Err(err) => {
                                error!("{}", err)
                            }
                        })
                    }
                }
            }
        }
    }
}

impl CustomDebugInfoParser for TILParser {
    fn is_valid(&self, _view: &BinaryView) -> bool {
        true
    }

    fn parse_info(&self, debug_info: &mut DebugInfo, bv: &BinaryView) {
        if let Some(idb_file) = get_open_filename_input("Select IDB", "*.til") {
            if let Ok(path) = idb_file.into_os_string().into_string() {
                if let Ok(til) = TILSection::parse_from_file(path) {
                    if let Some(types) = self.parse_all_types(bv, &til) {
                        let ok = types.iter().for_each(|x| match x {
                            Ok((str, ty)) => {
                                debug_info.add_type(std::str::from_utf8(str).unwrap(), ty);
                            }
                            Err(err) => {
                                error!("{}", err)
                            }
                        });
                        ok
                    }
                }
            }
        }
    }
}

struct IDBImport;
impl Command for IDBImport {
    fn action(&self, view: &BinaryView) {
        let idb_parser = DebugInfoParser::from_name("IDB Parser");
        if let Ok(parser) = idb_parser {
            let debug_info = parser.parse_debug_info(view, None);
            view.apply_debug_info(&debug_info)
        }
    }

    fn valid(&self, view: &BinaryView) -> bool {
        true
    }
}

struct TILImport;
impl Command for TILImport {
    fn action(&self, view: &BinaryView) {
        let idb_parser = DebugInfoParser::from_name("TIL Parser");
        if let Ok(parser) = idb_parser {
            let debug_info = parser.parse_debug_info(view, None);
            view.apply_debug_info(&debug_info)
        }
    }

    fn valid(&self, view: &BinaryView) -> bool {
        true
    }
}

#[no_mangle]
pub extern "C" fn CorePluginInit() -> bool {
    logger::init(log::LevelFilter::Debug);
    DebugInfoParser::register("IDB Parser", IDBParser {});
    DebugInfoParser::register("TIL Parser", TILParser {});
    binja::command::register(
        "IDB (Beta)\\Import Types From .i64",
        "Import IDB Types From File",
        IDBImport {},
    );
    binja::command::register(
        "IDB (Beta)\\Import IDA .til",
        "Import TIL Types From File",
        TILImport {},
    );
    true
}
