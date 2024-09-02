/-
# Naturals

Here we construct the natural numbers and proving their structures from scratch.

We start with declaring group theoretic structures including their properties.
This enables a template such that the Natural number type can implement the type
classes if and only if we can prove the properties at compile time.

## Group Theoretic Structures

We scope the group theoretic structures under the `Grp` namespace.
-/

namespace Grp

  /-
  ### Aplha of Some Type Universe

  We declare α as a generic type over a generic universe u. This enables any
  type in any universe to be defined for the following type classes that use α.
  Consider it syntax sugar.
  -/

  variable (α : Type u)

  /-
  ### Magma

  The magma type class admits only that there is an operation `op` that takes
  two elements of type α as inputs and returns one element of type α as output.

  Note that `α → α → α` is isomorphic to `(α, α) → α` via currying. More about
  this can be found [here](https://ncatlab.org/nlab/show/currying).
  -/

  class Magma where
    op : α → α → α

  /-
  ### Semigroup

  The semigroup type class extends a magma by admitting associativity such that
  applying the operation to three elements of type α returns the same result
  regardless of the order of application.

  That is to say that `(a ⋆ b) ⋆ c` is equal to `a ⋆ (b ⋆ c)`.
  -/

  class Semigroup extends Magma α where
    associativity : ∀ (a b c : α), op (op a b) c = op a (op b c)

  /-
  ### Monoid

  The monoid type class type class extends a semigroup by admitting that there
  exists an identity element `e` of type α such that the operation applies to it
  and any other element `a` of type α returns `a`.

  That is to say `e ⋆ a = a` and `a ⋆ e = a`.
  -/

  class Monoid extends Semigroup α where
    identity_element : α
    identity_left : ∀ (a : α), op identity_element a = a
    identity_right : ∀ (a : α), op a identity_element = a

  /-
  ### Group

  The group type class extends a monoid by admitting that for every element `a`
  of type α there exists an inverse element `a'` of type α such that the
  operation applied to the element and its inverse returns the identity element.

  That is to say `a ⋆ a' = e` and `a' ⋆ a = e`.
  -/

  class Group extends Monoid α where
    inverse : α → α
    inverse_left : ∀ (a : α), op (inverse a) a = identity_element
    inverse_right : ∀ (a : α), op a (inverse a) = identity_element

end Grp

/-
## Natural Numbers

We define the natural numbers as an inductive aka recursive type. The natural
numbers are either zero or the successor of another natural number. This enables
a theoretic construction of the infinite set of natural numbers `[0, ∞)`.

We follow the definition with the `open Natural` command to enable the use of
`zero` and `successor` without the `Natural.` prefix. Consider it syntax sugar.
-/
inductive Natural : Type
  | zero
  | successor : Natural → Natural

open Natural

/-
### Addition Function

We define the addition of natural numbers recursively. The addition of zero and
any term `n` of type Natural returns `n`. The addition of the successor of `m`
and `n` returns the successor of the sum of `m` and `n`.

That is to say, either we add zero to a number or we recursively transform a
nonzero number toward zero until we reach the base case of zero.
-/
def Natural.add : Natural → Natural → Natural
  | zero, n => n
  | successor m, n => successor (Natural.add m n)

/-
### Basic Addition Theorems
-/

/-
#### Add Zero

Adding any element of type Natural to zero returns the element.

We prove this by induction, first demonstrating the zero case through equality,
then the successor case with the hypothesis that the theorem holds for an
arbitrary natural number.

That is to say `add n zero = n`.
-/

theorem Natural.add_zero (n : Natural) : Natural.add n zero = n := by
  -- goal: `n + zero = n`
  -- tactic: prove by induction on `n`
  induction n with

  -- base case: `zero`
  | zero =>
    -- goal: `zero + zero = zero`
    -- tactic: rewrite `zero + zero` to `zero` with `Natural.add`
    rw [Natural.add]

  -- inductive case: `successor m` with hypothesis `hypothesis_n : m + zero = m`
  | successor m hypothesis_n =>
    -- goal: `successor m + zero = successor m`
    -- tactic: rewrite `successor m + zero` to `successor (m + zero)` with `Natural.add`
    rw [Natural.add]
    -- goal: `successor (m + zero) = successor m`
    -- tactic: rewrite `m + zero` to `m` with `hypothesis_n`
    rw [hypothesis_n]

/-
#### Zero Add

Adding zero to any element of type Natural returns the element.

Note that we can prove this by simply rewriting via the definition of addition.
This is because the zero case of addition (`add zero n = n`) can definitionally
prove this.

That is to say `add zero n = n`.
-/

theorem Natural.zero_add (n : Natural) : Natural.add zero n = n := by
  -- goal: `zero + n = n`
  -- tactic: rewrite `zero + n` to `n` with `Natural.add`
  rw [Natural.add]

/-
#### Add Is Associative

Addition of natural numbers is associative.

We prove this by induction, first demonstrating the zero case through the
previously proven `zero_add` theorem, then the successor case with the
hypothesis that the theorem holds for an arbitrary natural number.
-/

theorem add_is_associative (a b c : Natural) : Natural.add (Natural.add a b) c = Natural.add a (Natural.add b c) := by
  -- goal: `a + b + c = a + (b + c)`
  -- tactic: prove by induction on `a`
  induction a with

  -- base case: `zero`
  | zero =>
    -- goal: `zero + b + c = zero + (b + c)`
    -- tactic rewrite `zero + b` to `b` with `Natural.zero_add`
    rw [Natural.zero_add]
    -- goal: `b + c = zero + (b + c)`
    -- tactic: rewrite `zero + (b + c)` to `b + c` with `Natural.zero_add`
    rw [Natural.zero_add]

  -- inductive case: `successor m` with hypothesis `hypothesis_n : n + b + c = n + (b + c)`
  | successor n hypothesis_n =>
    -- goal: `successor n + b + c = successor n + (b + c)`
    -- tactic: rewrite `successor n + b` to `successor (n + b)` with `Natural.add`
    rw [Natural.add]
    -- goal: `successor (n + b) + c = successor n + (b + c)`
    -- tactic: rewrite `successor n + (b + c)` to `successor (n + (b + c))` with `Natural.add`
    rw [Natural.add]
    -- goal: `successor (n + b + c) = successor n + (b + c)`
    -- tactic: rewrite `n + b + c` to `n + (b + c)` with `Natural.add`
    rw [Natural.add]
    -- goal: `successor (n + b + c) = successor (n + (b + c))`
    -- tactic: rewrite `n + (b + c)` to `n + b + c` with `hypothesis_n`
    rw [hypothesis_n]

/-
## Type Class Instances

### Addition Over Natural Numbers

We define instances of the group theoretic type classes with the natural numbers
and the addition operation.

#### Magma

The natural numbers with addition form a magma. Since a magma only admits an
operation with no assumptions of algebraic strucutre, we only need to define the
`op` function.
-/

instance : Grp.Magma Natural where
  op := Natural.add

/-
#### Semigroup

The natural numbers with addition form a semigroup. Since a semigroup extends
a magma by admitting associativity, we use the `add_is_associative` theorem
proven above to define the `associativity` proof.
-/

instance : Grp.Semigroup Natural where
  associativity := add_is_associative

/-
#### Monoid

The natural numbers with addition form a monoid. Since a monoid extends a
semigroup by admitting an identity element and the property that the operation
applied to an element of type α (in this case Natural) and the identity element
returns the element regardless of order, we use `zero` as the identity element
and use the `zero_add` theorem proven above for `identity_left` and `add_zero`
theorem proven above for `identity_right`.
-/

instance : Grp.Monoid Natural where
  identity_element := zero
  identity_left := Natural.zero_add
  identity_right := Natural.add_zero

/-
#### Group

The natural numbers with addition do not form a group. This is because the
natural numbers with addition do not have inverses. Thus we use the `sorry`
tactic for each; these are generally used for temporary placeholders in proofs
that are not yet implemented. Here we use them to have the compiler generate a
warning instead of an error.

To construct a Group with addition, we would need either the Integer type which
admits negative numbers or a GaloisField which performs addition modulo a prime
number.
```lean
instance : Grp.Group Natural where
  inverse := sorry
  inverse_left := sorry
  inverse_right := sorry
```
-/
