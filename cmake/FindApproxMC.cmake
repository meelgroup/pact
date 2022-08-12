###############################################################################
# Top contributors (to current version):
#   Arijit Shaw
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find ApproxMC
# ApproxMC_FOUND - system has ApproxMC lib
# ApproxMC_INCLUDE_DIR - the ApproxMC include directory
# ApproxMC_LIBRARIES - Libraries needed to use ApproxMC
##

include(deps-helper)

find_package(approxmc ${ApproxMC_FIND_VERSION} QUIET)

set(ApproxMC_FOUND_SYSTEM FALSE)
if(approxmc_FOUND)
  set(ApproxMC_VERSION ${approxmc_VERSION})
  set(ApproxMC_FOUND_SYSTEM TRUE)
  add_library(ApproxMC INTERFACE IMPORTED GLOBAL)
  target_link_libraries(ApproxMC INTERFACE approxmc)
  # TODO(gereon): remove this when
  # https://github.com/msoos/approxmc/pull/645 is merged
  set_target_properties(
    ApproxMC PROPERTIES INTERFACE_INCLUDE_DIRECTORIES
                             "${APPROXMC_INCLUDE_DIRS}"
  )
endif()

if(NOT ApproxMC_FOUND_SYSTEM)
  set(ApproxMC_VERSION "5.8.0")

  check_ep_downloaded("ApproxMC-EP")
  if(NOT ApproxMC-EP_DOWNLOADED)
    check_auto_download("ApproxMC" "--no-approxmc")
  endif()

  include(ExternalProject)

  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set(LIBFILENAME "libapproxmcwin")
  else()
    set(LIBFILENAME "libapproxmc")
  endif()

  ExternalProject_Add(
    ApproxMC-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/msoos/approxmc/archive/refs/tags/${ApproxMC_VERSION}.tar.gz
    URL_HASH SHA1=f79dfa1ffc6c9c75b3a33f76d3a89a3df2b3f4c2
    PATCH_COMMAND
      patch <SOURCE_DIR>/src/packedmatrix.h
      ${CMAKE_CURRENT_LIST_DIR}/deps-utils/ApproxMC-patch-ba6f76e3.patch
    CMAKE_ARGS -DCMAKE_BUILD_TYPE=Release
               # make sure not to register with cmake
               -DCMAKE_EXPORT_NO_PACKAGE_REGISTRY=ON
               -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
               -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}
               -DENABLE_ASSERTIONS=OFF
               -DENABLE_PYTHON_INTERFACE=OFF
               # disable what is not needed
               -DNOBREAKID=ON
               -DNOM4RI=ON
               -DNOSQLITE=ON
               -DNOZLIB=ON
               -DONLY_SIMPLE=ON
               -DSTATICCOMPILE=ON
    BUILD_BYPRODUCTS <INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}/libapproxmc.a
  )
  # remove unused stuff to keep folder small
  ExternalProject_Add_Step(
    ApproxMC-EP cleanup
    DEPENDEES install
    COMMAND ${CMAKE_COMMAND} -E remove <BINARY_DIR>/approxmc_simple
    COMMAND ${CMAKE_COMMAND} -E remove <INSTALL_DIR>/bin/approxmc_simple
  )

  set(ApproxMC_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(ApproxMC_LIBRARIES "${DEPS_BASE}/${CMAKE_INSTALL_LIBDIR}/${LIBFILENAME}.a")

  add_library(ApproxMC STATIC IMPORTED GLOBAL)
  set_target_properties(
    ApproxMC PROPERTIES IMPORTED_LOCATION "${ApproxMC_LIBRARIES}"
  )
  set_target_properties(
    ApproxMC PROPERTIES INTERFACE_INCLUDE_DIRECTORIES
                             "${ApproxMC_INCLUDE_DIR}"
  )
endif()

set(ApproxMC_FOUND TRUE)

mark_as_advanced(ApproxMC_FOUND)
mark_as_advanced(ApproxMC_FOUND_SYSTEM)
mark_as_advanced(ApproxMC_INCLUDE_DIR)
mark_as_advanced(ApproxMC_LIBRARIES)

if(ApproxMC_FOUND_SYSTEM)
  message(
    STATUS
      "Found ApproxMC ${ApproxMC_VERSION}: ${ApproxMC_LIBRARIES}, ${ApproxMC_INCLUDE_DIR}"
  )
else()
  message(
    STATUS
      "Building ApproxMC ${ApproxMC_VERSION}: ${ApproxMC_LIBRARIES}"
  )
  add_dependencies(ApproxMC ApproxMC-EP)
endif()
