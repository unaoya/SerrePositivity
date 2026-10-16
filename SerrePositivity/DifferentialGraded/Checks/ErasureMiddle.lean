module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFirstEvaluation
public import Mathlib.Data.ZMod.Basic

/-! # unitorの全次数自然性と中間ε消去・先頭生成元の受入監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A]

example (P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    ((tensorLeftHom (𝟙_ (Complex A)) P Q).f p f).comp (Cochain.ofHom (λ_ Q).hom)
      (add_zero p) = (Cochain.ofHom (λ_ P).hom).comp f (zero_add p) :=
  leftUnitor_hom_cochain P Q p f
example (K P Q : Complex (ZMod 2)) (f : Cochain P Q 1) :
    (eraseMiddle (ZMod 2) K P).comp ((tensorLeftHom K P Q).f 1 f) (by omega) =
    -(((tensorLeftHom K (epsilonComplex (ZMod 2) ⊗ P)
      (epsilonComplex (ZMod 2) ⊗ Q)).f 1
        ((tensorLeftHom (epsilonComplex (ZMod 2)) P Q).f 1 f)).comp
          (eraseMiddle (ZMod 2) K Q) (show (1 : ℤ) + 1 = 2 by omega)) :=
  eraseMiddle_tail_anticommute (ZMod 2) K P Q f

#print axioms SerrePositivity.DifferentialGraded.tensorLeftHom_ofHom
#print axioms SerrePositivity.DifferentialGraded.complexLeftUnitor_inv_apply
#print axioms SerrePositivity.DifferentialGraded.leftUnitor_hom_generator
#print axioms SerrePositivity.DifferentialGraded.leftUnitor_inv_cochain
#print axioms SerrePositivity.DifferentialGraded.leftUnitor_hom_cochain
#print axioms SerrePositivity.DifferentialGraded.leftUnitor_hom_cochain_tensor
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseMiddle_tail_anticommute
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseMiddle_generator
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseFirst_generator
