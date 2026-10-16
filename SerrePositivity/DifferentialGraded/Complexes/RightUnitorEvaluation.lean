module
public import SerrePositivity.DifferentialGraded.Complexes.UnitorCochainNaturality

/-! # 右unitorの単位生成元上の成分 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma complexRightUnitor_inv_apply (P : Complex A) (i : ℤ) (x : P.X i) :
    (ρ_ P).inv.f i x = ιTensorObj P (𝟙_ (Complex A)) i 0 i (add_zero i)
      (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) := by
  change (rightUnitor' P).inv i x = _
  rw [rightUnitor'_inv]
  rfl

lemma rightUnitor_hom_generator (P : Complex A) (i : ℤ) (x : P.X i) :
    (ρ_ P).hom.f i (ιTensorObj P (𝟙_ (Complex A)) i 0 i (add_zero i)
      (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) = x := by
  rw [← complexRightUnitor_inv_apply]
  change ((ρ_ P).inv ≫ (ρ_ P).hom).f i x = x
  rw [Iso.inv_hom_id]
  rfl

end SerrePositivity.DifferentialGraded
