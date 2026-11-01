module
public import SerrePositivity.DifferentialGraded.Quotient.Erasure
public import Mathlib.Data.ZMod.Basic

/-! # 全次数tensor交差符号とε消去の反交換の受入監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A]

example (P P' Q Q' : Complex A) (f : Cochain P P' 1) (g : Cochain Q Q' 1) :
    ((tensorRightHom Q P P').f 1 f).comp ((tensorLeftHom P' Q Q').f 1 g)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom P Q Q').f 1 g).comp ((tensorRightHom Q' P P').f 1 f)
      (show (1 : ℤ) + 1 = 2 by omega)) := tensorCochain_odd_anticommute P P' Q Q' f g
example (P Q : Complex (ZMod 2)) (f : Cochain P Q 1) :
    (eraseRightTensor (ZMod 2) P).comp
      ((tensorLeftHom (𝟙_ (Complex (ZMod 2))) P Q).f 1 f) (by omega) =
    -(((tensorLeftHom (epsilonComplex (ZMod 2)) P Q).f 1 f).comp
      (eraseRightTensor (ZMod 2) Q) (show (1 : ℤ) + 1 = 2 by omega)) :=
  eraseRightTensor_tail_anticommute (ZMod 2) P Q f

#print axioms tensorCochain_interchange
#print axioms tensorCochain_odd_anticommute
#print axioms DGQuotient.eraseRightTensor_tail_anticommute
#print axioms DGQuotient.eraseRightTensor_prefixed_anticommute
