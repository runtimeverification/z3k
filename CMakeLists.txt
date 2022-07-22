project(Z3_KFRAMEWORK CXX)
cmake_minimum_required(VERSION 3.4)
find_package(Z3
  REQUIRED
)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

message(STATUS "Z3_FOUND: ${Z3_FOUND}")
message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
message(STATUS "Z3_DIR: ${Z3_DIR}")

add_executable(k-inference
	inference.cpp)

target_include_directories(k-inference PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(k-inference PRIVATE ${Z3_LIBRARIES})
