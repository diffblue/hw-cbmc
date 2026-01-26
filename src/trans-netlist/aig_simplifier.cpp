/*******************************************************************\

Module: AIG Simplifier

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "aig_simplifier.h"

literalt
apply_substitution(literalt l, const std::vector<literalt> &substitution)
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
  if(src.empty())
    return std::vector<literalt>();

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
    // Skip invalid equivalences
    if(l1.is_constant() && l2.is_constant())
      continue;

    // If one is constant, the other should map to that constant
    if(l1.is_constant())
    {
      if(l2.var_no() < num_nodes)
        substitution[l2.var_no()] = l1 ^ l2.sign();
      continue;
    }

    if(l2.is_constant())
    {
      if(l1.var_no() < num_nodes)
        substitution[l1.var_no()] = l2 ^ l1.sign();
      continue;
    }

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
      substitution[v2] = literalt(v1, signs_differ);
    }
    else if(v2 < v1)
    {
      // Replace v1 with v2
      substitution[v1] = literalt(v2, signs_differ);
    }
    // If v1 == v2, the equivalence is trivial (l1 ≡ l1 or l1 ≡ !l1)
    // The latter case (l1 ≡ !l1) would be a contradiction, ignore it
  }

  // Compute transitive closure of substitutions and propagate constraints
  // backwards: if an AND node is false, both inputs must be false
  // Repeat until no changes
  bool changed;
  do
  {
    changed = false;

    // Transitive closure
    for(std::size_t i = 0; i < num_nodes; i++)
    {
      literalt subst = substitution[i];
      if(subst.is_constant() || subst.var_no() == i)
        continue;

      // Follow the substitution chain
      literalt next = substitution[subst.var_no()] ^ subst.sign();
      if(next != subst)
      {
        substitution[i] = next;
        changed = true;
      }
    }

    // Backward propagation: if AND(a, b) = false, then a = false and b = false
    for(std::size_t i = 0; i < num_nodes; i++)
    {
      const auto &node = src.nodes[i];

      // Check if this is an AND node that's been set to false
      if(node.is_and() && substitution[i].is_false())
      {
        // Both inputs must be false
        // For node.a: if it's literalt(var, sign), we need var to map to
        // const_literal(false) XOR sign, so that var XOR sign = false
        if(!node.a.is_constant())
        {
          auto var_a = node.a.var_no();
          // We want node.a to evaluate to false
          // node.a = var_a XOR sign_a
          // For this to be false, var_a must be (false XOR sign_a)
          literalt new_val = const_literal(false) ^ node.a.sign();
          if(substitution[var_a] != new_val)
          {
            substitution[var_a] = new_val;
            changed = true;
          }
        }

        // Same for node.b
        if(!node.b.is_constant())
        {
          auto var_b = node.b.var_no();
          literalt new_val = const_literal(false) ^ node.b.sign();
          if(substitution[var_b] != new_val)
          {
            substitution[var_b] = new_val;
            changed = true;
          }
        }
      }
    }
  } while(changed);

  return substitution;
}

std::pair<aigt, substitutiont> apply_substitution(
  const aigt &src,
  const std::vector<literalt> &substitution)
{
  if(src.empty())
    return {aigt{}, {}};

  const auto num_nodes = src.number_of_nodes();
  PRECONDITION(substitution.size() == num_nodes);

  // Now rebuild the AIG with substitutions applied
  aigt dest;

  // Map from old node indices to new literals
  std::vector<literalt> old_to_new(num_nodes);

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

std::pair<aigt, substitutiont> aig_simplify(const aigt &src, const equivalencest &equivalences)
{
  auto substitution = aig_substitution(src, equivalences);
  return apply_substitution(src, substitution);
}
