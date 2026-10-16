module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureAdjacentInterchange
public import Mathlib.Data.ZMod.Basic

/-! # 先頭Homの結合則・最初のε消去の自然性・隣接消去の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

example {S : Set D} (b : S) (w : Word S) (i : ℕ) (x y : D) :
    (eraseFirst A D b w x y).comp (eraseFace A D w i x y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -((eraseFace A D (b :: w) (i + 1) x y).comp
      (eraseFirst A D b (w.eraseIdx i) x y) (show (1 : ℤ) + 1 = 2 by omega)) :=
  eraseFirst_face_anticommute A D b w i x y
example (b : (Set.univ : Set PUnit.{1})) :
    (eraseFirst (ZMod 2) PUnit.{1} b [b] PUnit.unit PUnit.unit).comp
      (eraseFirst (ZMod 2) PUnit.{1} b [] PUnit.unit PUnit.unit) (by omega) =
    -((eraseFace (ZMod 2) PUnit.{1} [b, b] 1 PUnit.unit PUnit.unit).comp
      (eraseFirst (ZMod 2) PUnit.{1} b [] PUnit.unit PUnit.unit)
      (show (1 : ℤ) + 1 = 2 by omega)) :=
  eraseFirst_adjacent_anticommute (ZMod 2) PUnit.{1} b b [] PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.tensorJoin_assoc
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_assoc
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseHead
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseHead_closed
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseMiddle_eq_tensorLeft
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.tensorJoin_eraseMiddle
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_eraseMiddle
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_eraseFirst
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseFirst_adjacent_anticommute
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseFirst_face_anticommute
