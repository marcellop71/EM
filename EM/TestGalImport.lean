import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Algebra.Field.ZMod

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

-- Check Group + Fintype instances
noncomputable example (f : (ZMod p)[X]) : Group f.Gal := inferInstance
noncomputable example (f : (ZMod p)[X]) : Fintype f.Gal := inferInstance
noncomputable example (f : (ZMod p)[X]) : Nat := Fintype.card f.Gal

-- Check natDegree + 1 polynomial
noncomputable example (f : (ZMod p)[X]) : Nat := f.natDegree

-- Check the Gal.card_of_separable theorem
#check @Polynomial.Gal.card_of_separable
