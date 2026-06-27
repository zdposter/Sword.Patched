# ---------------------------------------------------------------------
# Initialisation
# ---------------------------------------------------------------------

# Version change: Change line 17 only !
# Change it immediately after a release

define([svnversion], esyscmd([
    SVN_VERSION=$(svnversion -n 2>/dev/null || true)
    if test -z "$SVN_VERSION" || test "$SVN_VERSION" = "Unversioned directory"; then
        GIT_VERSION=$(git describe --always --abbrev=5 --exclude '*' 2>/dev/null || echo "Unknown-version")
        echo "$GIT_VERSION"
    else
        echo "$SVN_VERSION"
    fi
]))dnl
AC_INIT(sword, 1.9.0.svnversion, sword-bugs@crosswire.org, sword, http://crosswire.org/sword)
AC_CONFIG_SRCDIR(sword.bmp)
AC_PREREQ(2.52)
AC_REVISION($Revision: 1.45 $)

AC_CANONICAL_TARGET
AM_INIT_AUTOMAKE([subdir-objects])

AC_CONFIG_HEADERS([include/config.h])
AC_CONFIG_MACRO_DIR([m4])

# ---------------------------------------------------------------------
# Platform detection
# ---------------------------------------------------------------------
case $host_os in
    mingw* | msys*)
        # Allow libtool to pass DLL checks without exhaustive inspection
        export lt_cv_deplibs_check_method=pass_all
        # Tell the linker that we are building a Windows DLL
        # (un-comment when building a shared lib):
        # LDFLAGS="$LDFLAGS -no-undefined"
        is_windows_host=yes
        ;;
    cygwin*)
        is_windows_host=yes
        ;;
    *)
        is_windows_host=no
        ;;
esac

# ---------------------------------------------------------------------
# Check Programs
# ---------------------------------------------------------------------
CFLAGS=" $CFLAGS"
CXXFLAGS=" $CXXFLAGS"
AC_LANG([C++])
AC_PROG_CXX([g++ clang++])
AC_PROG_INSTALL
LT_INIT

AC_C_BIGENDIAN

# ----------------------------------------
# C++ related options
# ----------------------------------------
# Detect Clang compiler
AC_MSG_CHECKING([if compiling with clang])
AC_COMPILE_IFELSE(
[AC_LANG_PROGRAM([], [[
#ifndef __clang__
       not clang
#endif
]])],
[CLANG=yes], [CLANG=no])
AC_MSG_RESULT([$CLANG])

dnl **********************
dnl Turn on C++17 or newer
dnl **********************

CPLUSPLUS=
AX_CHECK_COMPILE_FLAG([-std=c++17], [CPLUSPLUS=17])
if test -z "$CPLUSPLUS"; then
  AC_MSG_WARN([Your compiler does not have the necessary C++17 support! Build may fail.])
fi

case "${host_os}" in
  cygwin*)
    CXXFLAGS="$CXXFLAGS -std=gnu++$CPLUSPLUS"
    ;;
  *-darwin* | *-macos10*)
    CXXFLAGS="$CXXFLAGS -std=c++$CPLUSPLUS"
    if test "x$CLANG" = "xyes"; then
      LDFLAGS="$LDFLAGS -stdlib=libc++"
    fi
    ;;
  *)
    CXXFLAGS="$CXXFLAGS -std=c++$CPLUSPLUS"
    ;;
esac

# ---------------------------------------------------------------------
# With options
# ---------------------------------------------------------------------
AC_ARG_WITH([zlib],
	[  --with-zlib             allow zlib compressed modules (default=yes)],, [with_zlib=yes])
AC_ARG_WITH([bzip2],
	[  --with-bzip2            allow bzip2 compressed modules (default=no)],, [with_bzip2=no])
AC_ARG_WITH([xz],
	[  --with-xz               allow xz compressed modules (default=no)],, [with_xz=no])
AC_ARG_WITH([icu],
	[  --with-icu              use ICU for unicode (default=yes)],, [with_icu=yes])
AC_ARG_WITH([icusword],
	[  --with-icusword         use custom SWORD ICU (default=no)],, [with_icusword=no])
AC_ARG_WITH([conf],
	[  --with-conf             install a new sword.conf (default=yes)],, [with_conf=yes])
AC_ARG_WITH([cxx11regex],
	[  --with-cxx11regex       build regex support using c++11 regex (default=no)],, [with_cxx11regex=no])
AC_ARG_WITH([cxx11time],
	[  --with-cxx11time        build time support using c++11 time (default=no)],, [with_cxx11time=no])
AC_ARG_WITH([curl],
	[  --with-curl             build install manager support using libcurl (default=yes)],, [with_curl=yes])
AC_ARG_WITH([curl_sftp],
	[  --with-curl_sftp        build install manager support using libcurl+sftp (requires --with-curl, default=yes)],, [with_curl_sftp=yes])
AC_ARG_WITH([internalregex],
	[  --with-internalregex    Compile using SWORDs internal copy of regex])
AC_ARG_WITH([icuregex],
	[  --with-icuregex         use ICU regex engine])
AC_ARG_WITH([xapian],
	[  --with-xapian           use xapian search engine (default=yes)],, [with_xapian=yes])
AC_ARG_WITH([gapi],
	[  --with-gapi             build SWORD with support for google apis],, [with_gapi=no])

# ---------------------------------------------------------------------
# Enable options
# ---------------------------------------------------------------------
AC_ARG_ENABLE([debug],
	[  --enable-debug          build debug library (default=no)],, [enable_debug=no])
AC_ARG_ENABLE([warnings],
	[  --enable-warnings       build with compiler warnings as errors (default=no)],, [enable_warnings=no])
AC_ARG_ENABLE([profile],
	[  --enable-profile        allow profiling (default=no)],, [enable_profile=no])
AC_ARG_ENABLE([profilefn],
	[  --enable-profilefn      allow functioncheck profiling (default=no)],, [enable_profilefn=no])
AC_ARG_ENABLE([tests],
	[  --enable-tests          build test programs (default=yes)],, [enable_tests=yes])
AC_ARG_ENABLE([utilities],
	[  --enable-utilities      build utilities (default=yes)],, [enable_utilities=yes])
AC_ARG_ENABLE([examples],
	[  --enable-examples       build examples (default=no)],, [enable_examples=no])
AC_ARG_ENABLE([logdebug],
	[  --disable-logd          strip log debug messages from code for optimization (default=no)], [disable_logdebug=yes], [disable_logdebug=no])
AC_ARG_ENABLE([loginfo],
	[  --disable-logi          strip log information messages from code for optimization (default=no)], [disable_loginfo=yes], [disable_loginfo=no])
AM_MAINTAINER_MODE

# ---------------------------------------------------------------------
# Debug and profile
# ---------------------------------------------------------------------

if test x$enable_debug = xyes; then
  GCJFLAGS="-g -O0"
  if test x$ac_cv_prog_cc_g = xyes; then
    AM_CFLAGS="-g3 -O0 -Wall"
  else
    AM_CFLAGS="-O0 -Wall"
  fi
  if test x$ac_cv_prog_cxx_g = xyes; then
    AM_CXXFLAGS="-g3 -O0 -Wall -Woverloaded-virtual"
  else
    AM_CXXFLAGS="-O0 -Wall -Woverloaded-virtual"
  fi
else
  AM_CFLAGS="-O3 -ffast-math"
  AM_CXXFLAGS="-O3 -ffast-math -Woverloaded-virtual"
fi

AM_CFLAGS="$AM_CFLAGS -fPIC"
AM_CXXFLAGS="$AM_CXXFLAGS -fPIC"

# Check for old vs new g++ template-depth syntax
saved_CXXFLAGS="$CXXFLAGS"
CXXFLAGS="$CXXFLAGS -ftemplate-depth=100"
AC_LANG_PUSH([C++])
AC_COMPILE_IFELSE([AC_LANG_PROGRAM([])],,[CXXFLAGS="$saved_CXXFLAGS -ftemplate-depth-100";])
AC_LANG_POP([C++])

# ---------------------------------------------------------------------
# Locate pkg-config (single, authoritative call)
# ---------------------------------------------------------------------
# PKG_PROG_PKG_CONFIG must be called once before any PKG_CHECK_MODULES.
# We do NOT gate anything on use_pkgconfig — pkg-config is effectively
# required on all supported platforms today.
PKG_PROG_PKG_CONFIG([0.14])
if test -z "$PKG_CONFIG"; then
  AC_MSG_WARN([pkg-config not found — library detection may be incomplete.])
  AC_MSG_WARN([Install pkg-config (Linux/macOS) or mingw-w64-*-pkgconf (MSYS2).])
fi

# ---------------------------------------------------------------------
# Augment PKG_CONFIG_PATH for known toolchain prefixes
# ---------------------------------------------------------------------
# Under MSYS2 the shell already exports PKG_CONFIG_PATH for the active
# environment (e.g. /mingw64/lib/pkgconfig).  We only add paths that
# are missing so we do not break the user's own setup.
#
# Helper: append $2 to $1 if not already present
m4_define([SWORD_PREPEND_PKGPATH], [
  case ":${PKG_CONFIG_PATH}:" in
    *":$2:"*) ;;
    *) PKG_CONFIG_PATH="$2${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}" ;;
  esac
])

case $host_os in
  mingw* | msys*)
    # Derive the mingw prefix from the compiler executable so the script
    # works for mingw32, mingw64, ucrt64, clang64, etc.
    sword_mingw_prefix=$(dirname $(dirname $($CXX -print-sysroot 2>/dev/null || echo "/mingw64")))
    # Fallback: try MINGW_PREFIX env var (set by MSYS2 shell)
    if test -z "$sword_mingw_prefix" || test "$sword_mingw_prefix" = "/"; then
      sword_mingw_prefix="${MINGW_PREFIX:-/mingw64}"
    fi
    SWORD_PREPEND_PKGPATH([PKG_CONFIG_PATH], [$sword_mingw_prefix/lib/pkgconfig])
    SWORD_PREPEND_PKGPATH([PKG_CONFIG_PATH], [$sword_mingw_prefix/share/pkgconfig])
    export PKG_CONFIG_PATH
    AC_MSG_NOTICE([MSYS2/MinGW PKG_CONFIG_PATH: $PKG_CONFIG_PATH])
    ;;
  *-darwin* | *-macos10*)
    # Homebrew — only set if the user has not already configured the path
    AC_CHECK_PROG([have_brew], [brew], [true], [false])
    if $have_brew; then
      brew_prefix=$(brew --prefix)
      SWORD_PREPEND_PKGPATH([PKG_CONFIG_PATH], [$brew_prefix/opt/icu4c/lib/pkgconfig])
      SWORD_PREPEND_PKGPATH([PKG_CONFIG_PATH], [$brew_prefix/opt/libarchive/lib/pkgconfig])
      SWORD_PREPEND_PKGPATH([PKG_CONFIG_PATH], [$brew_prefix/opt/curl/lib/pkgconfig])
      SWORD_PREPEND_PKGPATH([PKG_CONFIG_PATH], [$brew_prefix/opt/xapian/lib/pkgconfig])
      export PKG_CONFIG_PATH
    fi
    ;;
esac

# ---------------------------------------------------------------------
# Check libraries
# ---------------------------------------------------------------------
if test x$with_zlib = xyes; then
  AC_CHECK_LIB([z], [compress],, [with_zlib=no])
fi
if test x$with_zlib = xno; then
  AM_CFLAGS="$AM_CFLAGS -DEXCLUDEZLIB"
  AM_CXXFLAGS="$AM_CXXFLAGS -DEXCLUDEZLIB"
fi

if test x$with_bzip2 = xyes; then
  AC_CHECK_LIB([bz2], [BZ2_bzBuffToBuffCompress],, [with_bzip2=no])
fi
if test x$with_bzip2 = xno; then
  AM_CFLAGS="$AM_CFLAGS -DEXCLUDEBZIP2"
  AM_CXXFLAGS="$AM_CXXFLAGS -DEXCLUDEBZIP2"
fi

if test x$with_xz = xno; then
  AM_CFLAGS="$AM_CFLAGS -DEXCLUDEXZ"
  AM_CXXFLAGS="$AM_CXXFLAGS -DEXCLUDEXZ"
fi

AS_IF([test "x$with_internalregex" = "xyes"],
      [have_systemregex="no, using internal regex"],
      [AC_SEARCH_LIBS([regexec], [regex],
         [have_systemregex="yes"],
         [have_systemregex="no, using internal regex"])])

AS_IF([test "x$have_systemregex" = "xyes"],
      [with_internalregex="no"
       AC_MSG_NOTICE([Using system regex.h])],
      [with_internalregex="yes"
       AC_MSG_NOTICE([Using internal regex.h])])

# ---------------------------------------------------------------------
# Find CppUnit
# ---------------------------------------------------------------------
AM_PATH_CPPUNIT(1.8.0)
AM_CONDITIONAL([HAVE_CPPUNIT], [test "x$CPPUNIT_LIBS" != x])

# ---------------------------------------------------------------------
# Find XZ / lzma using pkg-config
# ---------------------------------------------------------------------
if test x$with_xz = xyes; then
  PKG_CHECK_MODULES([XZ], [liblzma], [
    with_xz=yes
    AC_DEFINE([HAVE_XZ], [1], [Define to 1 if you have XZ/LZMA support])
    AM_CFLAGS="$AM_CFLAGS $XZ_CFLAGS"
    AM_CXXFLAGS="$AM_CXXFLAGS $XZ_CFLAGS"
  ], [
    with_xz=no
  ])
fi
AC_SUBST([XZ_CFLAGS])
AC_SUBST([XZ_LIBS])

# ---------------------------------------------------------------------
# Find ICU
# ---------------------------------------------------------------------
# Strategy:
#  1. Try pkg-config (works on Linux, macOS/Homebrew, MSYS2).
#  2. Fall back to icu-config script (older installs).
#  3. Fall back to AC_CHECK_LIB with the naming convention used on
#     each platform (icuuc / sicuuc on Windows static builds).
# ---------------------------------------------------------------------
ICU_LIBS=
ICU_CFLAGS=
ICU_IOLIBS=

if test x$with_icu = xyes; then
  # --- attempt 1: pkg-config ---
  PKG_CHECK_MODULES([ICU], [icu-uc >= 52.1 icu-i18n >= 52.1], [
    with_icu=yes
    AM_CXXFLAGS="$AM_CXXFLAGS $ICU_CFLAGS -D_ICU_"
    AM_CFLAGS="$AM_CFLAGS $ICU_CFLAGS -D_ICU_"
    LIBS="$LIBS $ICU_LIBS"
    PKG_CHECK_MODULES([ICUIO], [icu-io], [
      ICU_IOLIBS="$ICUIO_LIBS"
      LIBS="$LIBS $ICUIO_LIBS"
    ], [
      ICU_IOLIBS=
    ])
  ], [
    # --- attempt 2: icu-config script ---
    AC_PATH_PROG([ICU_CONFIG], [icu-config], [no])
    if test "x$ICU_CONFIG" != "xno"; then
      AC_MSG_NOTICE([ICU pkg-config not found; using icu-config script])
      ICU_CFLAGS=$($ICU_CONFIG --cppflags-searchpath 2>/dev/null)
      ICU_LIBS=$($ICU_CONFIG --ldflags 2>/dev/null)
      ICU_IOLIBS=$($ICU_CONFIG --ldflags-icuio 2>/dev/null)
      if test -n "$ICU_LIBS"; then
        with_icu=yes
        AM_CXXFLAGS="$AM_CXXFLAGS $ICU_CFLAGS -D_ICU_"
        AM_CFLAGS="$AM_CFLAGS $ICU_CFLAGS -D_ICU_"
        LIBS="$LIBS $ICU_LIBS $ICU_IOLIBS"
      else
        AC_MSG_WARN([icu-config found but returned no flags — disabling ICU])
        with_icu=no
      fi
    else
      # --- attempt 3: direct library probe ---
      # MSYS2 ships icuuc/icuin; some static Windows builds use sicuuc/sicuin
      AC_MSG_NOTICE([No icu-config; probing ICU libraries directly])
      AC_LANG_PUSH([C++])
      saved_LIBS="$LIBS"
      icu_found=no
      for icu_uc_lib in icuuc sicuuc; do
        for icu_in_lib in icuin icui18n sicuin; do
          LIBS="$saved_LIBS -l$icu_uc_lib -l$icu_in_lib"
          AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <unicode/ustring.h>]],
                         [[u_strlen(NULL);]])],
            [icu_found=yes; break], [])
          test "x$icu_found" = xyes && break
        done
        test "x$icu_found" = xyes && break
      done
      AC_LANG_POP([C++])
      if test "x$icu_found" = xyes; then
        with_icu=yes
        ICU_LIBS="-l$icu_uc_lib -l$icu_in_lib"
        AM_CXXFLAGS="$AM_CXXFLAGS -D_ICU_"
        AM_CFLAGS="$AM_CFLAGS -D_ICU_"
        # Probe for icuio / sicuio
        AC_CHECK_LIB([icuio], [main],
          [ICU_IOLIBS="-licuio"; LIBS="$LIBS -licuio"],
          [AC_CHECK_LIB([sicuio], [main],
            [ICU_IOLIBS="-lsicuio"; LIBS="$LIBS -lsicuio"],
            [ICU_IOLIBS=])])
      else
        LIBS="$saved_LIBS"
        AC_MSG_WARN([ICU libraries not found — compiling without ICU support])
        with_icu=no
      fi
    fi
  ])
fi

if test x$with_icusword = xyes; then
  AM_CXXFLAGS="$AM_CXXFLAGS -D_ICUSWORD_"
  AM_CFLAGS="$AM_CFLAGS -D_ICUSWORD_"
fi

# ---------------------------------------------------------------------
# Compiler warning / profiling flags
# ---------------------------------------------------------------------
if test x$enable_warnings = xyes; then
  AM_CFLAGS="$AM_CFLAGS -Werror"
  AM_CXXFLAGS="$AM_CXXFLAGS -Werror -Woverloaded-virtual"
fi

if test x$enable_profile = xyes; then
  AM_CFLAGS="$AM_CFLAGS -pg"
  AM_CXXFLAGS="$AM_CXXFLAGS -pg"
fi

if test x$enable_profilefn = xyes; then
  AM_CFLAGS="$AM_CFLAGS -g -finstrument-functions"
  AM_CXXFLAGS="$AM_CXXFLAGS -g -finstrument-functions"
  LIBS="$LIBS -g -finstrument-functions -lfnccheck"
fi

# ---------------------------------------------------------------------
# Find libcurl for install manager support
# ---------------------------------------------------------------------
# Strategy:
#  1. pkg-config (preferred; works everywhere including MSYS2).
#  2. curl-config script (fallback for non-standard installs).
#  3. Direct AC_CHECK_LIB (last resort).
# ---------------------------------------------------------------------
with_internalftplib=no
CURL_LIBS=
CURL_AM_CFLAGS=

if test x$with_curl = xyes; then
  # --- attempt 1: pkg-config ---
  PKG_CHECK_MODULES([LIBCURL], [libcurl], [
    have_libcurl=yes
    CURL_AM_CFLAGS="$LIBCURL_CFLAGS"
    CURL_LIBS="$LIBCURL_LIBS"
  ], [
    have_libcurl=no
  ])

  if test "x$have_libcurl" = xno; then
    # --- attempt 2: curl-config script ---
    AC_PATH_PROG([CURL_CONFIG], [curl-config], [no])
    if test "x$CURL_CONFIG" != xno; then
      AC_MSG_NOTICE([libcurl pkg-config not found; using curl-config script])
      CURL_AM_CFLAGS=$($CURL_CONFIG --cflags 2>/dev/null)
      CURL_LIBS=$($CURL_CONFIG --libs 2>/dev/null)
      if test -n "$CURL_LIBS"; then
        have_libcurl=yes
      fi
    fi
  fi

  if test "x$have_libcurl" = xno; then
    # --- attempt 3: direct probe ---
    AC_MSG_NOTICE([curl-config not found; probing libcurl directly])
    AC_CHECK_LIB([curl], [curl_easy_init],
      [have_libcurl=yes; CURL_LIBS="-lcurl"],
      [have_libcurl=no])
  fi

  if test "x$have_libcurl" = xyes; then
    AC_MSG_NOTICE([curl found — remote install options available])
    AM_CXXFLAGS="$AM_CXXFLAGS -DCURLAVAILABLE $CURL_AM_CFLAGS"
    AM_CFLAGS="$AM_CFLAGS -DCURLAVAILABLE $CURL_AM_CFLAGS"
    LIBS="$LIBS $CURL_LIBS"
    with_curl=yes

    # Check for SFTP protocol support
    if test x$with_curl_sftp = xyes; then
      curl_sftp_supported=no
      # Try pkg-config / curl-config first, then a compile check
      if test "x$CURL_CONFIG" != xno && test "x$CURL_CONFIG" != x; then
        if test x$($CURL_CONFIG --protocols 2>/dev/null | grep -i SFTP | wc -l) = x1; then
          curl_sftp_supported=yes
        fi
      else
        # pkg-config path: probe with a feature-test compile
        AC_LANG_PUSH([C++])
        AC_COMPILE_IFELSE([AC_LANG_PROGRAM(
          [[#include <curl/curl.h>]],
          [[
            #ifndef CURL_VERSION_LIBZ
            #error no sftp info
            #endif
            (void)curl_version_info(CURLVERSION_NOW);
          ]])],
          [curl_sftp_supported=yes], [curl_sftp_supported=no])
        AC_LANG_POP([C++])
      fi
      if test "x$curl_sftp_supported" = xyes; then
        AM_CXXFLAGS="$AM_CXXFLAGS -DCURLSFTPAVAILABLE"
        AM_CFLAGS="$AM_CFLAGS -DCURLSFTPAVAILABLE"
      else
        with_curl_sftp=no
      fi
    fi
  else
    AC_MSG_WARN([libcurl not found — compiling without curl support, using internal ftplib])
    with_curl="no, using internal ftplib"
    with_curl_sftp=no
    with_internalftplib=yes
  fi
else
  with_curl="no, using internal ftplib"
  with_curl_sftp=no
  with_internalftplib=yes
fi

# ---------------------------------------------------------------------
# Optional CXX11 flags
# ---------------------------------------------------------------------
if test x$with_cxx11regex = xyes; then
  AM_CXXFLAGS="$AM_CXXFLAGS -DUSECXX11REGEX"
fi

if test x$with_cxx11time = xyes; then
  AM_CXXFLAGS="$AM_CXXFLAGS -DUSECXX11TIME"
fi

if test x$disable_logdebug = xyes; then
  AM_CXXFLAGS="$AM_CXXFLAGS -DSTRIPLOGD"
fi

if test x$disable_loginfo = xyes; then
  AM_CXXFLAGS="$AM_CXXFLAGS -DSTRIPLOGI"
fi

# ---------------------------------------------------------------------
# Find CLucene for lucene searching support
# ---------------------------------------------------------------------
# NOTE: The $libdir include hack is preserved — on some distros (e.g.
# Fedora multilib) CLucene places generated headers under /usr/lib[64]/.
# Strategy:
#  1. pkg-config for CLucene 2.x (libclucene-core).
#  2. Legacy ACX_CLUCENE m4 macro for 0.x.
# Both checks happen AFTER PKG_CONFIG_PATH is fully set up (above).
# ---------------------------------------------------------------------
with_clucene=no
CLUCENE_LIBS=

PKG_CHECK_MODULES([CLUCENE2], [libclucene-core >= 2.3], [
  AC_MSG_NOTICE([CLucene 2.x found — lucene searching options available])
  AM_CXXFLAGS="$AM_CXXFLAGS $CLUCENE2_CFLAGS -DUSELUCENE -DCLUCENE2 -I$libdir"
  AM_CFLAGS="$AM_CFLAGS $CLUCENE2_CFLAGS -DUSELUCENE -DCLUCENE2 -I$libdir"
  LIBS="$LIBS $CLUCENE2_LIBS"
  with_clucene="yes 2.x"
  CLUCENE_LIBS="$CLUCENE2_LIBS"
], [
  # Fall back to old ACX_CLUCENE macro (0.9.x / 0.x)
  ACX_CLUCENE
  if test "x$CLUCENE_LIBS" != x; then
    AC_MSG_NOTICE([CLucene 0.x found — lucene searching options available])
    AM_CXXFLAGS="$AM_CXXFLAGS $CLUCENE_CXXFLAGS -DUSELUCENE -I$libdir"
    AM_CFLAGS="$AM_CFLAGS -DUSELUCENE -I$libdir"
    LIBS="$LIBS $CLUCENE_LIBS"
    with_clucene="yes 0.x"
  else
    AC_MSG_WARN([CLucene not found — lucene searching unavailable])
  fi
])

# ---------------------------------------------------------------------
# Find ICU regex support (depends on ICU being enabled)
# ---------------------------------------------------------------------
if test x$with_icuregex = xyes; then
  if test x$with_icu = xno; then
    with_icuregex="requested but ICU not enabled"
  else
    AM_CFLAGS="$AM_CFLAGS -DUSEICUREGEX"
    AM_CXXFLAGS="$AM_CXXFLAGS -DUSEICUREGEX"
  fi
else
  with_icuregex="no"
fi

# ---------------------------------------------------------------------
# Find Xapian search engine
# ---------------------------------------------------------------------
# Strategy:
#  1. pkg-config (xapian-core) — works on Linux, macOS/Homebrew, MSYS2.
#  2. xapian-config script — ships with source tarballs and some distros.
#  3. Direct AC_CHECK_LIB with C++ link test (C++ libraries need special care).
# ---------------------------------------------------------------------
XAPIAN_CFLAGS=
XAPIAN_LIBS=

if test x$with_xapian = xyes; then
  # --- attempt 1: pkg-config ---
  PKG_CHECK_MODULES([XAPIAN], [xapian-core], [
    with_xapian=yes
  ], [
    with_xapian=no
    # --- attempt 2: xapian-config script ---
    AC_PATH_PROG([XAPIAN_CONFIG], [xapian-config], [no])
    if test "x$XAPIAN_CONFIG" != xno; then
      AC_MSG_NOTICE([xapian pkg-config not found; using xapian-config script])
      XAPIAN_CFLAGS=$($XAPIAN_CONFIG --cxxflags 2>/dev/null)
      XAPIAN_LIBS=$($XAPIAN_CONFIG --libs 2>/dev/null)
      if test -n "$XAPIAN_LIBS"; then
        with_xapian=yes
      fi
    fi

    if test x$with_xapian = xno; then
      # --- attempt 3: direct C++ link probe ---
      AC_MSG_NOTICE([xapian-config not found; probing xapian library directly])
      AC_LANG_PUSH([C++])
      saved_LIBS="$LIBS"
      LIBS="$saved_LIBS -lxapian"
      AC_LINK_IFELSE([AC_LANG_PROGRAM(
        [[#include <xapian.h>]],
        [[Xapian::Database db;]])],
        [with_xapian=yes; XAPIAN_LIBS="-lxapian"],
        [LIBS="$saved_LIBS"
         AC_MSG_WARN([Xapian library not found — xapian searching unavailable])])
      AC_LANG_POP([C++])
    fi
  ])

  if test x$with_xapian = xyes; then
    AM_CFLAGS="$AM_CFLAGS -DUSEXAPIAN $XAPIAN_CFLAGS"
    AM_CXXFLAGS="$AM_CXXFLAGS -DUSEXAPIAN $XAPIAN_CFLAGS"
    LIBS="$LIBS $XAPIAN_LIBS"
    # Xapian supersedes CLucene; note this in the summary
    if test "x$with_clucene" != xno; then
      with_clucene="$with_clucene; but using XAPIAN instead"
    fi
  fi
fi

AC_SUBST([XAPIAN_CFLAGS])
AC_SUBST([XAPIAN_LIBS])

# ---------------------------------------------------------------------
# Miscellaneous function checks
# ---------------------------------------------------------------------
AC_CHECK_FUNCS([vsnprintf], [have_vsnprintf="yes"])

# ---------------------------------------------------------------------
# Alter global conf directory only if not /etc
# ---------------------------------------------------------------------
if test "x$sysconfdir" = "x/etc"; then
  dir_confdef="no"
else
  dir_confdef="yes"
fi

# ---------------------------------------------------------------------
# Version number decomposition
# ---------------------------------------------------------------------
changequote(<<,>>)
V1=`expr $VERSION : '\([0-9]*\)\.[0-9]*\.*[0-9]*\.*[0-9]*'`
V2=`expr $VERSION : '[0-9]*\.\([0-9]*\)\.*[0-9]*\.*[0-9]*'`
V3=`expr $VERSION : '[0-9]*\.[0-9]*\.*\([0-9]*\)\.*[0-9]*'`
V4=`expr $VERSION : '[0-9]*\.[0-9]*\.*[0-9]*\.*\([0-9]*\)'`
changequote([,])

SWORD_VERSION_STR=$VERSION
SWORD_VERSION_MAJOR=$V1
SWORD_VERSION_MINOR=$V2
SWORD_VERSION_MICRO=$V3
if test "$V4" = "" ; then V4=0; fi
SWORD_VERSION_NANO=$V4

if test "$V2" -le 9 ; then V2=0$V2 ; fi
if test "$V3" -le 9 ; then V3=00$V3 ; elif test "$V3" -le 99 ; then V3=0$V3 ; fi
if test "$V4" -le 9 ; then V4=00$V4 ; elif test "$V4" -le 99 ; then V4=0$V4 ; fi
SWORD_VERSION_NUM=$V1$V2$V3$V4

# ---------------------------------------------------------------------
# Compiler warning suppression
# ---------------------------------------------------------------------
echo "Checking optional compiler warning flags..."
m4_foreach(WARN_CHECK, [-Wno-address, -Wno-nonnull-compare],
[
  AX_CHECK_COMPILE_FLAG([WARN_CHECK], [WARNINGS_OFF="$WARNINGS_OFF WARN_CHECK"], [], [-Werror])
])
AM_CXXFLAGS="$AM_CXXFLAGS $WARNINGS_OFF"

# ---------------------------------------------------------------------
# Substitute variables into makefiles
# ---------------------------------------------------------------------
AC_SUBST([SWORD_VERSION_NUM])
AC_SUBST([SWORD_VERSION_STR])
AC_SUBST([SWORD_VERSION_MAJOR])
AC_SUBST([SWORD_VERSION_MINOR])
AC_SUBST([SWORD_VERSION_MICRO])
AC_SUBST([SWORD_VERSION_NANO])

AC_SUBST([with_zlib])
AC_SUBST([with_bzip2])
AC_SUBST([with_xz])
AC_SUBST([with_icu])
AC_SUBST([with_icusword])
AC_SUBST([with_conf])
AC_SUBST([dir_confdef])
AC_SUBST([CC])
AC_SUBST([enable_debug])
AC_SUBST([enable_profile])

AC_SUBST([AM_CXXFLAGS])
AC_SUBST([AM_CFLAGS])

AC_SUBST([target_cpu])
AC_SUBST([target_vendor])
AC_SUBST([target_os])
AC_SUBST([target_system])
AC_SUBST([target_mingw32])

AC_SUBST([CURL_LIBS])
AC_SUBST([ICU_LIBS])
AC_SUBST([ICU_CFLAGS])
AC_SUBST([ICU_IOLIBS])
AC_SUBST([CLUCENE_LIBS])

# ---------------------------------------------------------------------
# Conditional variables
# ---------------------------------------------------------------------
AM_CONDITIONAL([HAVE_LIBZ],         [test x$with_zlib = xyes])
AM_CONDITIONAL([HAVE_BZIP2],        [test x$with_bzip2 = xyes])
AM_CONDITIONAL([HAVE_XZ],           [test x$with_xz = xyes])
AM_CONDITIONAL([HAVE_ICU],          [test x$with_icu = xyes])
AM_CONDITIONAL([HAVE_ICUSWORD],     [test x$with_icusword = xyes])
AM_CONDITIONAL([HAVE_VSNPRINTF],    [test x$have_vsnprintf = xyes])
AM_CONDITIONAL([USELUCENE],         [test "x$with_clucene" != xno])
AM_CONDITIONAL([SHAREDLIB],         [test x$enable_shared = xyes])
AM_CONDITIONAL([INSTCONF],          [test x$with_conf = xyes])
AM_CONDITIONAL([USECXX11REGEX],     [test x$with_cxx11regex = xyes])
AM_CONDITIONAL([USEICUREGEX],       [test x$with_icuregex = xyes])
AM_CONDITIONAL([USECXX11TIME],      [test x$with_cxx11time = xyes])
AM_CONDITIONAL([STRIPLOGD],         [test x$disable_logdebug = xyes])
AM_CONDITIONAL([STRIPLOGI],         [test x$disable_loginfo = xyes])
AM_CONDITIONAL([WITHCURL],          [test x$with_curl = xyes])
AM_CONDITIONAL([WITHGAPI],          [test x$with_gapi = xyes])
AM_CONDITIONAL([WITHCURLSFTP],      [test x$with_curl_sftp = xyes])
AM_CONDITIONAL([INTERNALFTPLIB],    [test x$with_internalftplib = xyes])
AM_CONDITIONAL([USE_INTERNAL_REGEX],[test x$with_internalregex = xyes])
AM_CONDITIONAL([CONFDEF],           [test x$dir_confdef = xyes])
AM_CONDITIONAL([BUILDTESTS],        [test x$enable_tests = xyes])
AM_CONDITIONAL([BUILDUTILS],        [test x$enable_utilities = xyes])
AM_CONDITIONAL([BUILDEXAMPLES],     [test x$enable_examples = xyes])

# USE_PKGCONF is kept for Makefile.am compatibility; always true when
# PKG_CONFIG was found.
AM_CONDITIONAL([USE_PKGCONF],       [test -n "$PKG_CONFIG"])

# ---------------------------------------------------------------------
# Final output
# ---------------------------------------------------------------------
AC_CONFIG_FILES([Makefile lib/Makefile tests/Makefile tests/testsuite/Makefile tests/cppunit/Makefile utilities/Makefile examples/Makefile examples/cmdline/Makefile examples/tasks/Makefile utilities/diatheke/Makefile sword.pc include/swversion.h sword.spec])
AC_OUTPUT

echo
echo
echo "Configuration:"
echo     ""
echo     " Settings:"
echo     "     LIBDIR:               $libdir"
echo     "     DEBUG:                $enable_debug"
echo     "     PROFILE:              $enable_profile"
echo     "     BUILD TESTS:          $enable_tests"
echo     "     BUILD EXAMPLES:       $enable_examples"
echo     "     BUILD UTILITIES:      $enable_utilities"
echo     "     STRIP LOG DEBUG:      $disable_logdebug"
echo     "     STRIP LOG INFO:       $disable_loginfo"
echo     ""
echo     " Dependencies for standard use:"
echo     "     REGEX:                $have_systemregex"
echo     "     ZLIB:                 $with_zlib"
echo     "     LIBICU:               $with_icu"
echo     "     LIBCURL:              $with_curl"
echo     "     CLUCENE-CORE:         $with_clucene"
echo     ""
echo     " Optional / Experimental:"
echo     "     LIBCURL SFTP:         $with_curl_sftp"
echo     "     BZIP2:                $with_bzip2"
echo     "     XZ:                   $with_xz"
echo     "     ICUSWORD:             $with_icusword"
echo     "     ICU-REGEX:            $with_icuregex"
echo     "     CXX11-REGEX:          $with_cxx11regex"
echo     "     CXX11-TIME:           $with_cxx11time"
echo     "     XAPIAN-CORE:          $with_xapian"
echo     "     GAPI:                 $with_gapi"
