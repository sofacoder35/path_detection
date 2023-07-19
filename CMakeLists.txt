cmake_minimum_required(VERSION 3.14)
project(parallel_union_find)
set(CMAKE_CXX_STANDARD 17)
add_executable(mytest main.cpp)
add_executable(mytest0 tests/performance_tests/find_all_sccs_on_the_fly.cpp)
include_directories(
        ${CMAKE_CURRENT_SOURCE_DIR}/graph_node
        ${CMAKE_CURRENT_SOURCE_DIR}/storage
        ${CMAKE_CURRENT_SOURCE_DIR}/algorithm
        ${CMAKE_CURRENT_SOURCE_DIR}/union_find/blocking
        ${CMAKE_CURRENT_SOURCE_DIR}/wfc
        ${CMAKE_CURRENT_SOURCE_DIR}/wfc/utility
)
