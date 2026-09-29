/*******************************************************************\

Module: Verilog Preprocessor Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/message.h>

#include <testing-utils/use_catch.h>
#include <verilog/verilog_preprocessor.h>

#include <list>
#include <sstream>

/// Run the Verilog preprocessor on the given source, and return the
/// preprocessed output. The preprocessor emits `line directives relative
/// to the given file name; we use a fixed name so the expected output is
/// stable. These tests deliberately avoid `include/+incdir+, which depend
/// on the file system and are covered by the regression suite instead.
static std::string preprocess(
  const std::string &source,
  const std::string &file_name = "test.v",
  const std::list<std::string> &initial_defines = {})
{
  std::istringstream in(source);
  std::ostringstream out;
  null_message_handlert message_handler;
  const std::list<std::string> include_paths;

  verilog_preprocessort preprocessor(
    in, out, message_handler, file_name, include_paths, initial_defines);

  preprocessor.preprocessor();

  return out.str();
}

SCENARIO("Verilog preprocessor `define")
{
  GIVEN("object-like and function-like macros")
  {
    auto out = preprocess(
      "`define basic\n"
      "`basic\n"
      "`define with_value value\n"
      "`with_value\n"
      "`define uses_previous `with_value\n"
      "`uses_previous\n"
      "`define with_parameter(a, b, c) a-b-c\n"
      "`with_parameter(x, y, z)\n"
      "`with_parameter(x, y, `with_value)\n"
      "`with_parameter (moo, foo, bar)\n"
      "`define no_parameter (1+2)\n"
      "`no_parameter\n",
      "define1.v");

    THEN("the macros are expanded")
    {
      REQUIRE(
        out ==
        "`line 1 \"define1.v\" 0\n"
        "\n"
        "\n"
        "\n"
        "value\n"
        "\n"
        "value\n"
        "\n"
        "x-y-z\n"
        "x-y-value\n"
        "moo-foo-bar\n"
        "\n"
        "(1+2)\n");
    }
  }
}

SCENARIO("Verilog preprocessor multi-line `define")
{
  GIVEN("a macro whose body spans multiple lines via backslash")
  {
    auto out = preprocess(
      "`define foo A \\\n"
      "B \\\n"
      "C\n"
      "`foo\n",
      "multi-line-define1.v");

    THEN("the line breaks are preserved in the expansion")
    {
      REQUIRE(
        out ==
        "`line 1 \"multi-line-define1.v\" 0\n"
        "\n"
        "`line 4 \"multi-line-define1.v\" 0\n"
        "A \n"
        "B \n"
        "C\n"
        "`line 5 \"multi-line-define1.v\" 0\n");
    }
  }

  GIVEN("a multi-line macro body that contains a single-line comment")
  {
    auto out = preprocess(
      "// The \"BAR2\" is part of the define\n"
      "`define FOO BAR1 \\\n"
      "  // comment \\\n"
      "  BAR2\n"
      "\n"
      "`FOO\n",
      "define-with-comment1.v");

    THEN("the body after the comment continuation is retained")
    {
      REQUIRE(
        out ==
        "`line 1 \"define-with-comment1.v\" 0\n"
        "\n"
        "\n"
        "`line 5 \"define-with-comment1.v\" 0\n"
        "\n"
        "BAR1 \n"
        "  \n"
        "  BAR2\n"
        "`line 7 \"define-with-comment1.v\" 0\n");
    }
  }
}

SCENARIO("Verilog preprocessor macro default parameters")
{
  GIVEN("function-like macros with default parameter values")
  {
    // Per IEEE 1800-2017 22.5.1, `define M(A, B=x) makes B default to x
    // when the actual argument is omitted or empty. Defaults may contain
    // commas nested in (), [] or {}.
    auto out = preprocess(
      "`define M(A, B=x) A+B\n"
      "`M(a, b)\n"
      "`M(a)\n"
      "`M(a, )\n"
      "`define N(A=1, B=2, C=3) A-B-C\n"
      "`N()\n"
      "`N(9)\n"
      "`N(9, 8)\n"
      "`N(9, 8, 7)\n"
      "`define P(A, B={1,2}) A-B\n"
      "`P(p)\n"
      "`P(p, {3,4})\n",
      "macro_default_param1.sv");

    THEN("omitted or empty arguments fall back to the default")
    {
      REQUIRE(
        out ==
        "`line 1 \"macro_default_param1.sv\" 0\n"
        "\n"
        "a+b\n"
        "a+x\n"
        "a+x\n"
        "\n"
        "1-2-3\n"
        "9-2-3\n"
        "9-8-3\n"
        "9-8-7\n"
        "\n"
        "p-{1,2}\n"
        "p-{3,4}\n");
    }
  }
}

SCENARIO("Verilog preprocessor double backtick")
{
  GIVEN("a `` token paste following a macro")
  {
    auto out = preprocess(
      "`define something foobar\n"
      "`something``_else\n",
      "double_backtick1.sv");

    THEN("the macro and the trailing text are pasted together")
    {
      REQUIRE(
        out ==
        "`line 1 \"double_backtick1.sv\" 0\n"
        "\n"
        "foobar_else\n");
    }
  }
}

SCENARIO("Verilog preprocessor `ifdef/`elsif/`else")
{
  GIVEN("an `ifdef whose condition is defined, with a trailing `elsif")
  {
    auto out = preprocess(
      "`define X 1\n"
      "`ifdef X\n"
      "IFDEF\n"
      "`elsif Y\n"
      "ELSIF\n"
      "`endif",
      "elsif1.v");

    THEN("only the `ifdef branch is emitted")
    {
      REQUIRE(out.find("IFDEF") != std::string::npos);
      REQUIRE(out.find("ELSIF") == std::string::npos);
    }
  }

  GIVEN("an `ifdef whose condition is undefined but an `elsif matches")
  {
    auto out = preprocess(
      "`define Y 1\n"
      "`ifdef X\n"
      "`elsif Y\n"
      "ELSIF\n"
      "`endif",
      "elsif2.v");

    THEN("only the `elsif branch is emitted")
    {
      REQUIRE(out.find("ELSIF") != std::string::npos);
      REQUIRE(out.find("IFDEF") == std::string::npos);
    }
  }

  GIVEN("a chain where the first branch matches via a command-line define")
  {
    // `ifdef A matches (A defined via -D), so only BRANCH_A is emitted,
    // and neither the later `elsif branches nor the `else are emitted.
    auto out = preprocess(
      "`ifdef A\n"
      "BRANCH_A\n"
      "`elsif B\n"
      "BRANCH_B\n"
      "`elsif C\n"
      "BRANCH_C\n"
      "`else\n"
      "BRANCH_ELSE\n"
      "`endif",
      "elsif3.v",
      {"A"});

    THEN("only the matched branch is emitted")
    {
      REQUIRE(out.find("BRANCH_A") != std::string::npos);
      REQUIRE(out.find("BRANCH_B") == std::string::npos);
      REQUIRE(out.find("BRANCH_C") == std::string::npos);
      REQUIRE(out.find("BRANCH_ELSE") == std::string::npos);
    }
  }
}

SCENARIO("Verilog preprocessor inline nested `ifdef")
{
  GIVEN("a nested `ifdef on the same line as a FALSE enclosing `ifdef")
  {
    // Both conditionals are closed by the two `endif on the same line, so
    // the conditional nesting returns to depth zero and the code that
    // follows the block must be emitted.
    auto out = preprocess(
      "`ifdef NOT_DEFINED `ifdef ALSO_NOT_DEFINED `endif `endif\n"
      "module main;\n"
      "endmodule",
      "nested_ifdef1.sv");

    THEN("the trailing code is emitted")
    {
      REQUIRE(out.find("module main;") != std::string::npos);
      REQUIRE(out.find("endmodule") != std::string::npos);
    }
  }
}

SCENARIO("Verilog preprocessor `undefineall")
{
  GIVEN("macros that are removed by `undefineall")
  {
    auto out = preprocess(
      "`define FOO 123\n"
      "`define BAR 456\n"
      "`undefineall\n"
      "`ifdef FOO\n"
      "FAIL\n"
      "`else\n"
      "PASS\n"
      "`endif",
      "undefineall1.v");

    THEN("the previously defined macro is no longer defined")
    {
      REQUIRE(out.find("PASS") != std::string::npos);
      REQUIRE(out.find("FAIL") == std::string::npos);
    }
  }
}

SCENARIO("Verilog preprocessor `__FILE__ and `__LINE__")
{
  GIVEN("a source that references `__FILE__ and `__LINE__")
  {
    auto out = preprocess(
      "module main;\n"
      "\n"
      "  initial $display(\"Internal error: null handle at %s, line %d.\",\n"
      "    `__FILE__, `__LINE__);\n"
      "\n"
      "endmodule",
      "file1.v");

    THEN("they expand to the file name and line number")
    {
      REQUIRE(out.find("\"file1.v\", 4);") != std::string::npos);
    }
  }
}

SCENARIO("Verilog preprocessor command-line defines")
{
  GIVEN("defines passed as initial defines")
  {
    auto out = preprocess(
      "`ifdef SOMETHING\n"
      "A\n"
      "`endif\n"
      "`ifdef OTHER\n"
      "B\n"
      "`endif\n"
      "`ELSE",
      "cmdline_define1.v",
      {"SOMETHING", "ELSE=foo"});

    THEN("the defined branch is emitted and the macro is expanded")
    {
      REQUIRE(out.find("A") != std::string::npos);
      REQUIRE(out.find("foo") != std::string::npos);
      REQUIRE(out.find("B") == std::string::npos);
    }
  }
}

SCENARIO("Verilog preprocessor error handling")
{
  GIVEN("an unknown preprocessor directive")
  {
    THEN("the preprocessor throws")
    {
      // The command-line front-end catches this and exits with code 1.
      REQUIRE_THROWS(preprocess("`something", "unknown_directive.v"));
    }
  }
}
