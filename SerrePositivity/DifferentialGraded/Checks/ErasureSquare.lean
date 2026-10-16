module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureSquare
public import Mathlib.Data.ZMod.Basic

/-! # 任意二位置の反交換・有限和相殺・全消去作用素二乗零の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

example {S : Set D} (w : Word S) (i j : ℕ) (hij : i ≤ j) (x y : D) :
    doubleFace A D w i j x y = negateDoubleFace A D (doubleFace A D w (j + 1) i x y) :=
  doubleFace_swap_of_le A D w i j hij x y
example [Small.{u} D] (S : Set D) (x y : D) :
    (erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega) = 0 :=
  erasure_square_zero A D S x y
example :
    (erasure (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit).comp
      (erasure (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit)
      (show (1 : ℤ) + 1 = 2 by omega) = 0 :=
  erasure_square_zero (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.DoubleFace
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.doubleFace
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.negateDoubleFace
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.negateDoubleFace_involutive
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixDoubleFace
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixDoubleFace_negate
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.doubleFace_cons_succ
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.doubleFace_cons_zero
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.doubleFace_swap_of_le
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.includeDoubleFace
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.includeDoubleFace_negate
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.erasurePair
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.erasurePair_swap_of_le
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.erasurePair_swap
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.erasurePair_double_sum_zero
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathCochain_ext
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.erasure_square_precomp_double_sum
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.erasure_square_zero
