/*******************************************************************\

Module: Command File Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <ebmc/command_file.h>
#include <testing-utils/use_catch.h>

#include <cstdlib>
#include <string>

#ifdef _WIN32
#  include <stdlib.h>
static void set_env(const char *name, const char *value)
{
  _putenv_s(name, value);
}
static void unset_env(const char *name)
{
  _putenv_s(name, "");
}
#else
static void set_env(const char *name, const char *value)
{
  setenv(name, value, 1);
}
static void unset_env(const char *name)
{
  unsetenv(name);
}
#endif

SCENARIO("expand_environment_variables: no variables")
{
  REQUIRE(expand_environment_variables("hello world") == "hello world");
  REQUIRE(expand_environment_variables("") == "");
  REQUIRE(
    expand_environment_variables("/path/to/file.sv") == "/path/to/file.sv");
}

SCENARIO("expand_environment_variables: $VAR form")
{
  // Set a known environment variable for testing
  set_env("EBMC_TEST_VAR", "myvalue");

  REQUIRE(expand_environment_variables("$EBMC_TEST_VAR") == "myvalue");
  REQUIRE(
    expand_environment_variables("prefix/$EBMC_TEST_VAR/suffix") ==
    "prefix/myvalue/suffix");
  REQUIRE(
    expand_environment_variables("$EBMC_TEST_VAR$EBMC_TEST_VAR") ==
    "myvaluemyvalue");

  unset_env("EBMC_TEST_VAR");
}

SCENARIO("expand_environment_variables: ${VAR} form")
{
  set_env("EBMC_TEST_VAR", "braced");

  REQUIRE(expand_environment_variables("${EBMC_TEST_VAR}") == "braced");
  REQUIRE(
    expand_environment_variables("${EBMC_TEST_VAR}_tail") == "braced_tail");
  REQUIRE(
    expand_environment_variables("head_${EBMC_TEST_VAR}") == "head_braced");

  unset_env("EBMC_TEST_VAR");
}

SCENARIO("expand_environment_variables: undefined variable expands to empty")
{
  // Make sure this variable is not set
  unset_env("EBMC_UNDEFINED_VAR_12345");

  REQUIRE(expand_environment_variables("$EBMC_UNDEFINED_VAR_12345") == "");
  REQUIRE(
    expand_environment_variables("a/$EBMC_UNDEFINED_VAR_12345/b") == "a//b");
  REQUIRE(expand_environment_variables("${EBMC_UNDEFINED_VAR_12345}") == "");
}

SCENARIO("expand_environment_variables: literal $ preserved in edge cases")
{
  // lone $ at end of string
  REQUIRE(expand_environment_variables("cost$") == "cost$");

  // $ followed by non-identifier character
  REQUIRE(expand_environment_variables("$!foo") == "$!foo");
  REQUIRE(expand_environment_variables("$ space") == "$ space");

  // unclosed ${
  REQUIRE(expand_environment_variables("${UNCLOSED") == "${UNCLOSED");
}

SCENARIO("expand_environment_variables: mixed usage")
{
  set_env("EBMC_TEST_DIR", "/opt/libs");
  set_env("EBMC_TEST_FILE", "top.sv");

  REQUIRE(
    expand_environment_variables("$EBMC_TEST_DIR/${EBMC_TEST_FILE}") ==
    "/opt/libs/top.sv");
  REQUIRE(
    expand_environment_variables("-I$EBMC_TEST_DIR/include") ==
    "-I/opt/libs/include");

  unset_env("EBMC_TEST_DIR");
  unset_env("EBMC_TEST_FILE");
}
