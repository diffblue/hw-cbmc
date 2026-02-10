/*******************************************************************\

Module: AIG Simplifier

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "aig_simplifier.h"

literalt apply_substitution(literalt l, const substitutiont &substitution)
{
  if(l.is_constant())
    return l;

  auto var_no = l.var_no();
  PRECONDITION(var_no < substitution.size());

  // Get the replacement literal and apply the sign
  return substitution[var_no] ^ l.sign();
}

/// Simplify an AND node after substitution
/// \param a: First input literal (after substitution)
/// \param b: Second input literal (after substitution)
/// \param dest: The destination AIG to add the node to
/// \return The literal representing the simplified AND
static literalt simplify_and(literalt a, literalt b, aigt &dest)
{
  // Constant propagation
  if(a.is_false() || b.is_false())
    return const_literal(false);

  if(a.is_true())
    return b;

  if(b.is_true())
    return a;

  // a AND a = a
  if(a == b)
    return a;

  // a AND !a = false
  if(a == !b)
    return const_literal(false);

  // Normalize: smaller variable number first
  if(b.var_no() < a.var_no())
    std::swap(a, b);

  // Create the AND node
  return dest.new_and_node(a, b);
}

std::vector<literalt>
aig_substitution(const aigt &src, const equivalencest &equivalences)
{
  const auto num_nodes = src.number_of_nodes();

  // Build a substitution map: for each variable, what literal should it
  // be replaced with? Initially, each variable maps to itself.
  std::vector<literalt> substitution;
  substitution.reserve(num_nodes);

  for(std::size_t i = 0; i < num_nodes; i++)
    substitution.emplace_back(i, false);

  // Process equivalences. For each equivalence (l1, l2), we want to
  // replace references to the larger variable with the smaller one.
  for(const auto &[l1, l2] : equivalences)
  {
    // Skip equivalences that are constraints
    if(l1.is_constant() || l2.is_constant())
      continue;

    // Both are non-constant
    // l1 ≡ l2 means: v1 ^ s1 ≡ v2 ^ s2
    // We replace the larger variable with the smaller one
    auto v1 = l1.var_no();
    auto v2 = l2.var_no();

    if(v1 >= num_nodes || v2 >= num_nodes)
      continue;

    // Compute the sign relationship: if l1 ≡ l2, then
    // v1 should map to v2 ^ (s1 ^ s2), or vice versa
    bool signs_differ = l1.sign() != l2.sign();

    if(v1 < v2)
    {
      // Replace v2 with v1
      substitution[v2] = literalt{v1, signs_differ};
    }
    else if(v2 < v1)
    {
      // Replace v1 with v2
      substitution[v1] = literalt{v2, signs_differ};
    }
    // If v1 == v2, the equivalence is trivial (l1 ≡ l1 or l1 ≡ !l1)
    // The latter case (l1 ≡ !l1) would be a contradiction, ignore it
  }

  return substitution;
}

std::pair<aigt, substitutiont>
apply_substitution(const aigt &src, const substitutiont &substitution)
{
  const auto num_nodes = src.number_of_nodes();
  PRECONDITION(substitution.size() == num_nodes);

  // Now rebuild the AIG with substitutions applied
  aigt dest;

  // Map from old node indices to new literals
  std::vector<literalt> old_to_new{num_nodes};

  for(std::size_t i = 0; i < num_nodes; i++)
  {
    const auto &node = src.nodes[i];

    // First, check what this node is substituted with
    literalt subst = substitution[i];

    if(subst.is_constant())
    {
      // This node is equivalent to a constant
      old_to_new[i] = subst;
      continue;
    }

    if(subst.var_no() != i)
    {
      // This node is equivalent to another (smaller) node
      // Use what that node maps to, applying the sign
      old_to_new[i] = old_to_new[subst.var_no()] ^ subst.sign();
      continue;
    }

    // This node is a representative (maps to itself), we need to create it
    if(node.is_input())
    {
      // primary input
      old_to_new[i] = dest.new_input();
    }
    else
    {
      // AND node - substitute inputs and simplify
      literalt new_a = apply_substitution(node.a, old_to_new);
      literalt new_b = apply_substitution(node.b, old_to_new);
      old_to_new[i] = simplify_and(new_a, new_b, dest);
    }
  }

  // Re-number the labeling
  for(const auto &[label, lit] : src.labeling)
  {
    dest.labeling[label] = apply_substitution(lit, old_to_new);
  }

  return {dest, old_to_new};
}

std::pair<aigt, substitutiont>
aig_simplify(const aigt &src, const equivalencest &equivalences)
{
  auto substitution = aig_substitution(src, equivalences);
  return apply_substitution(src, substitution);
}
