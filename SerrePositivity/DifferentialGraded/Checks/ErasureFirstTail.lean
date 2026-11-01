module
public import SerrePositivity.DifferentialGraded.Quotient.Composition
public import Mathlib.Data.ZMod.Basic

/-! # 実際の後方faceの自然性・先頭εとの反交換の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

example {S : Set D} (b c : S) (w : Word S) (i : ℕ) (x y : D) :
    (eraseFirst A D b (c :: w) x y).comp
      (eraseFace A D (c :: w) (i + 1) x y) (show (1 : ℤ) + 1 = 2 by omega) =
    -((eraseFace A D (b :: c :: w) (i + 2) x y).comp
      (eraseFirst A D b ((c :: w).eraseIdx (i + 1)) x y)
      (show (1 : ℤ) + 1 = 2 by omega)) := eraseFirst_tail_anticommute A D b c w i x y
example (b : (Set.univ : Set PUnit.{1})) :
    (eraseFirst (ZMod 2) PUnit.{1} b [b, b] PUnit.unit PUnit.unit).comp
      (eraseFace (ZMod 2) PUnit.{1} [b, b] 1 PUnit.unit PUnit.unit) (by omega) =
    -((eraseFace (ZMod 2) PUnit.{1} [b, b, b] 2 PUnit.unit PUnit.unit).comp
      (eraseFirst (ZMod 2) PUnit.{1} b [b] PUnit.unit PUnit.unit)
      (show (1 : ℤ) + 1 = 2 by omega)) :=
  eraseFirst_tail_anticommute (ZMod 2) PUnit.{1} b b [b] 0 PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.tensorJoin_hom_naturality
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_tail_hom
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_suffix_hom
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_eraseFace_succ
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseFirst_tail_anticommute
