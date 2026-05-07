cmake_minimum_required(VERSION 3.23)
project(diplomovka)

set(CMAKE_CXX_STANDARD 14)

add_executable(solver_tests CNF.h TestSolver.cpp Solver.h Solver.cpp Inferencer.cpp Inferencer.h
        Theory.h translator.cpp translator.h Unifier.h
        Unifier.cpp)
