cmake_minimum_required(VERSION 3.18 FATAL_ERROR)
project(nuterm)

find_package(Torch REQUIRED)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${TORCH_CXX_FLAGS}")

add_executable(pytorch_tests pytorch_tests.cpp)
target_link_libraries(pytorch_tests "${TORCH_LIBRARIES}")
set_property(TARGET pytorch_tests PROPERTY CXX_STANDARD 17)

add_executable(nuterm nuterm_main.cpp vcd_parser.cpp training.cpp)
target_link_libraries(nuterm "${TORCH_LIBRARIES}")
set_property(TARGET nuterm PROPERTY CXX_STANDARD 17)
