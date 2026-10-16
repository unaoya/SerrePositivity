module
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainFactors
public import Mathlib.Data.ZMod.Basic

/-! # 右tensor合成保存とassociatorの全次数自然性の受入監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

example (K P Q T : Complex A) (f : Cochain P Q (-1)) (g : Cochain Q T 1) :
    (tensorRightHom K P T).f 0 (f.comp g (by decide)) =
      ((tensorRightHom K P Q).f (-1) f).comp ((tensorRightHom K Q T).f 1 g) (by decide) :=
  tensorRightHom_cochain_comp K P Q T (-1) 1 0 (by decide) f g

example (K P Q R : Complex (ZMod 2)) (f : Cochain P Q 1) :
    ((tensorRightHom R (K ⊗ P) (K ⊗ Q)).f 1
      ((tensorLeftHom K P Q).f 1 f)).comp (Cochain.ofHom (α_ K Q R).hom) (add_zero 1) =
    (Cochain.ofHom (α_ K P R).hom).comp
      ((tensorLeftHom K (P ⊗ R) (Q ⊗ R)).f 1
        ((tensorRightHom R P Q).f 1 f)) (zero_add 1) :=
  associator_hom_cochain_middle K P Q R 1 f

#print axioms SerrePositivity.DifferentialGraded.tensorRightHom_apply_of_sum
#print axioms SerrePositivity.DifferentialGraded.tensorRightHom_cochain_comp
#print axioms SerrePositivity.DifferentialGraded.tensorRightHom_ofHom
#print axioms SerrePositivity.DifferentialGraded.leftTripleCochain_ext
#print axioms SerrePositivity.DifferentialGraded.associator_hom_cochain_left
#print axioms SerrePositivity.DifferentialGraded.associator_hom_cochain_middle
