cmake_minimum_required(VERSION 3.9 FATAL_ERROR)

project(idb_import_plugin)

file(GLOB PLUGIN_SOURCES
        ${PROJECT_SOURCE_DIR}/Cargo.toml
        ${PROJECT_SOURCE_DIR}/src/*.rs)

if(CMAKE_BUILD_TYPE MATCHES Debug)
    set(TARGET_DIR ${PROJECT_BINARY_DIR}/target/debug)
    set(CARGO_OPTS --target-dir=${PROJECT_BINARY_DIR}/target)
else()
    set(TARGET_DIR ${PROJECT_BINARY_DIR}/target/release)
    set(CARGO_OPTS --target-dir=${PROJECT_BINARY_DIR}/target --release)
endif()

set(OUTPUT_FILE ${CMAKE_SHARED_LIBRARY_PREFIX}idb_import_plugin${CMAKE_SHARED_LIBRARY_SUFFIX})
set(OUTPUT_PATH ${BN_CORE_PLUGIN_DIR}/${OUTPUT_FILE})

add_custom_target(idb_import_plugin ALL DEPENDS ${OUTPUT_PATH})

if (BN_INTERNAL_BUILD)
    add_dependencies(idb_import_plugin binaryninjacore)
    set($ENV{BINARYNINJADIR} $<TARGET_FILE_DIR:binaryninjacore>)
endif()

find_program(RUSTUP_PATH rustup REQUIRED HINTS ~/.cargo/bin)
set(RUSTUP_COMMAND ${RUSTUP_PATH} run ${CARGO_STABLE_VERSION} cargo build)

if(APPLE)
    if(UNIVERSAL)
        if(CMAKE_BUILD_TYPE MATCHES Debug)
            set(AARCH64_LIB_PATH ${PROJECT_BINARY_DIR}/target/aarch64-apple-darwin/debug/${OUTPUT_FILE})
            set(X86_64_LIB_PATH ${PROJECT_BINARY_DIR}/target/x86_64-apple-darwin/debug/${OUTPUT_FILE})
        else()
            set(AARCH64_LIB_PATH ${PROJECT_BINARY_DIR}/target/aarch64-apple-darwin/release/${OUTPUT_FILE})
            set(X86_64_LIB_PATH ${PROJECT_BINARY_DIR}/target/x86_64-apple-darwin/release/${OUTPUT_FILE})
        endif()

        add_custom_command(
                OUTPUT ${OUTPUT_PATH}
                COMMAND ${CMAKE_COMMAND} -E env
                MACOSX_DEPLOYMENT_TARGET=10.14
                ${RUSTUP_COMMAND} --target=aarch64-apple-darwin ${CARGO_OPTS}
                COMMAND ${CMAKE_COMMAND} -E env
                MACOSX_DEPLOYMENT_TARGET=10.14
                ${RUSTUP_COMMAND} --target=x86_64-apple-darwin ${CARGO_OPTS}
                COMMAND ${CMAKE_COMMAND} -E copy ${AARCH64_LIB_PATH} ${OUTPUT_PATH}-aarch
                COMMAND ${CMAKE_COMMAND} -E copy ${X86_64_LIB_PATH} ${OUTPUT_PATH}
                WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                DEPENDS ${PLUGIN_SOURCES})
    else()
        if(CMAKE_BUILD_TYPE MATCHES Debug)
            set(LIB_PATH ${PROJECT_BINARY_DIR}/target/debug/${OUTPUT_FILE})
        else()
            set(LIB_PATH ${PROJECT_BINARY_DIR}/target/release/${OUTPUT_FILE})
        endif()

        add_custom_command(
                OUTPUT ${OUTPUT_PATH}
                COMMAND ${CMAKE_COMMAND} -E env
                MACOSX_DEPLOYMENT_TARGET=10.14
                ${RUSTUP_COMMAND} ${CARGO_OPTS}
                COMMAND ${CMAKE_COMMAND} -E copy ${LIB_PATH} ${OUTPUT_PATH}
                WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                DEPENDS ${PLUGIN_SOURCES})
    endif()
elseif(WIN32)
    add_custom_command(
            OUTPUT ${OUTPUT_PATH}
            COMMAND ${CMAKE_COMMAND} -E env ${RUSTUP_COMMAND} ${CARGO_OPTS}
            COMMAND ${CMAKE_COMMAND} -E copy ${TARGET_DIR}/${OUTPUT_FILE} ${OUTPUT_PATH}
            WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
            DEPENDS ${PLUGIN_SOURCES})
else()
    add_custom_command(
            OUTPUT ${OUTPUT_PATH}
            COMMAND ${CMAKE_COMMAND} -E env ${RUSTUP_COMMAND} ${CARGO_OPTS}
            COMMAND ${CMAKE_COMMAND} -E copy ${TARGET_DIR}/${OUTPUT_FILE} ${OUTPUT_PATH}
            WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
            DEPENDS ${PLUGIN_SOURCES})
endif()
