#include <util/invariant_utils.h>

int FLEX_CLASS_NAME::lex()
{
  return FLEX_FN(lex)(state);
}

char *FLEX_CLASS_NAME::text()
{
  return FLEX_FN(get_text)(state);
}

std::size_t FLEX_CLASS_NAME::leng() const
{
  return FLEX_FN(get_leng)(state);
}

int FLEX_CLASS_NAME::lineno() const
{
  return FLEX_FN(get_lineno)(state);
}

void FLEX_CLASS_NAME::lineno(int lineno)
{
  return FLEX_FN(set_lineno)(lineno, state);
}

void FLEX_CLASS_NAME::init_extra(void *extra)
{
  auto result = FLEX_FN(lex_init_extra)(extra, &state);
  CHECK_RETURN(result == 0);
}

void FLEX_CLASS_NAME::destroy()
{
  FLEX_FN(lex_destroy)(state);
}
