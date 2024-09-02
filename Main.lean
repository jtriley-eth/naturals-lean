import «Naturals»

/-
# Naturals

This is a collection of theorems and definitions over the natural numbers. Of
course, Lean4 includes the `Nat` type in its standard library and prelude. It
should be used in practice. This is an experiment in creating and proving the
properties of the natural numbers from scratch in a way that's designed to be
maximally readable.

Some knowlege of Lean4 syntax is assumed, though familiarity with its proving
system is not. Each line of code is reasonably explained, both in formal terms
and more colloquial terms.

Each module is written to be read as an article, from top to bottom.

Start from [`Naturals/Basic.lean`](./Naturals/Basic.lean).
-/

def main : IO Unit :=
  do IO.println (String.append (String.append
    "Where's the code execution?"
    "Turns out, proving the natural numbers is done at compile time.")
    "Thus successful compilation implies proof correctness!")
