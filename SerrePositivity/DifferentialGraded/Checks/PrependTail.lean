module
public import SerrePositivity.DifferentialGraded.Quotient.Append
public import Mathlib.Data.ZMod.Basic

/-! # associatorの全次数自然性と先頭Hom合成の後方自然性の受入監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

example (P Q R S : Complex (ZMod 2)) (p : ℤ) (f : Cochain R S p) :
    ((tensorLeftHom (P ⊗ Q) R S).f p f).comp
      (Cochain.ofHom (α_ P Q S).hom) (add_zero p) =
    (Cochain.ofHom (α_ P Q R).hom).comp
      ((tensorLeftHom P (Q ⊗ R) (Q ⊗ S)).f p
        ((tensorLeftHom Q R S).f p f)) (zero_add p) :=
  associator_hom_cochain_right P Q R S p f

#print axioms SerrePositivity.DifferentialGraded.associator_hom_cochain_right
#print axioms SerrePositivity.DifferentialGraded.associator_inv_cochain_right
#print axioms SerrePositivity.DifferentialGraded.tensorLeftHom_cochain_naturality
#print axioms SerrePositivity.DifferentialGraded.tensorJoin_cochain_naturality
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseFace_cons_succ
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_tail_cochain
