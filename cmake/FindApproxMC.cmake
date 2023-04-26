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

set(ApproxMC_FOUND_SYSTEM FALSE)

#TODO (arijit) if approxmc is already built somewhere,
#  cmake here can understand that, but can't link to the
#  library or headers. fix this. the commented out section
#  below should work.

#find_package(approxmc ${ApproxMC_FIND_VERSION} QUIET)

#if(approxmc_FOUND)
  #set(ApproxMC_VERSION ${approxmc_VERSION})
  #set(ApproxMC_FOUND_SYSTEM TRUE)
  #add_library(ApproxMC INTERFACE IMPORTED GLOBAL)
  #target_link_libraries(ApproxMC INTERFACE approxmc)
  #set_target_properties(
    #ApproxMC PROPERTIES INTERFACE_INCLUDE_DIRECTORIES
                             #"${APPROXMC_INCLUDE_DIRS}"
  #)
#endif()

if(NOT ApproxMC_FOUND_SYSTEM)
  set(ApproxMC_VERSION "4.1.11")

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
    BUILD_IN_SOURCE ON
    URL https://github.com/meelgroup/approxmc/archive/refs/tags/${ApproxMC_VERSION}.tar.gz
    URL_HASH SHA1=e4e7a8587ba0c07b60d180a6584968828194ff82
    CMAKE_ARGS -DCMAKE_BUILD_TYPE=Release
               # make sure not to register with cmake
               -DCMAKE_EXPORT_NO_PACKAGE_REGISTRY=ON
               -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
               -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}
               -DENABLE_ASSERTIONS=OFF
               -DENABLE_PYTHON_INTERFACE=OFF
               # disable what is not needed
               -DSTATICCOMPILE=OFF
    BUILD_BYPRODUCTS <INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}/libapproxmc.so
  )

  set(ApproxMC_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(ApproxMC_LIBRARIES "${DEPS_BASE}/${CMAKE_INSTALL_LIBDIR}/${LIBFILENAME}.so")

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
