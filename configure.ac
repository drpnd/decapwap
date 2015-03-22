#
# $Id: configure.ac,v 3ed1b5b71f04 2011/03/16 06:49:37 Hirochika $
#
# Copyright (c) 2010-2011 Scyphus Solutions Co.,Ltd. All rights reserved.
# Authors:
#      Hirochika Asai  <asai@scyphus.co.jp>
#

AC_PREREQ(2.59)
AC_INIT([decapwap], [0.1.0], [bug@scyphus.co.jp])
AC_CONFIG_SRCDIR([decapwap.c])
AC_CONFIG_HEADER([config.h])

# Get hostname and other information.
AC_CANONICAL_BUILD
AC_CANONICAL_HOST
AC_CANONICAL_TARGET

AM_INIT_AUTOMAKE
AC_SUBST(SUBDIRS)

# Checks for arguments
AC_ARG_ENABLE(debug,
  [  --enable-debug    Turn on debugging [default no]],
  [case "${enableval}" in
    yes) debug=yes; AC_MSG_RESULT(Checking for debug... yes); AC_DEFINE(DEBUG, 1, debugging option) ;;
    no)  debug=no;;
    *) AC_MSG_ERROR(bad value ${enableval} for --enable-debug) ;;
  esac],[debug=no])
AM_CONDITIONAL(DEBUG, test x$debug = xtrue)

# Checks for hosts
case $host_os in
     freebsd*)
	AC_DEFINE(TARGET_FREEBSD, 1, running on FreeBSD)
	arch=freebsd
	;;
     netbsd*)
	AC_DEFINE(TARGET_NETBSD, 1, running on NetBSD)
	arch=netbsd
	;;
     darwin*)
	AC_DEFINE(TARGET_DARWIN, 1, running on Mac OS X)
	arch=darwin
	;;
     linux*)
	AC_DEFINE(TARGET_LINUX, 1, running on Linux)
	arch=linux
     	;;
     *) ;;
esac


# Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_LN_S
AC_PROG_RANLIB
AC_PROG_INSTALL

# Checks for libraries.
if test -z "$LIBPCAP_LIB"; then
  AC_CHECK_LIB(pcap, pcap_open_live,
    pcap_ok=yes,
    pcap_ok=no)
  if test "$pcap_ok" = yes; then
    AC_MSG_CHECKING(for pcap.h)
    AC_CHECK_HEADER(pcap.h,
      PCAP='pcap'; LIBPCAP_LIB='-lpcap', AC_MSG_ERROR(pcap.h not found))
  else
    AC_MSG_ERROR(libpcap not found)
  fi
fi
AC_SUBST(PCAP)
AC_SUBST(LIBPCAP_LIB)


# Checks for header files.
AC_HEADER_STDC
AC_CHECK_HEADERS([stdint.h stdlib.h string.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T

# Checks for library functions.
AC_FUNC_MALLOC

AC_CONFIG_FILES([Makefile])
AC_OUTPUT

echo "
decapwap configuration
--------------------
decapwap version        : ${PACKAGE_VERSION}
host operationg system  : ${host_os}
source code location    : ${srcdir}
compiler                : ${CC}
compiler flags          : ${CFLAGS}
linker flags            : ${LDFLAGS} ${LIBS}
"
