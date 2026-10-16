module
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation

/-! # 両側に閉単位射を挿入する操作の純tensor表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable {A : Type u} [CommRing A]

lemma unitSandwich_apply (H E : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (i : ℤ) (x : E.X i) :
    ((λ_ E).inv ≫ (e ⊗ₘ ((ρ_ E).inv ≫ (𝟙 E ⊗ₘ e)))).f i x =
    ιTensorObj H (E ⊗ H) 0 i i (zero_add i)
      (e.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) ⊗ₜ[A]
        ιTensorObj E H i 0 i (add_zero i)
          (x ⊗ₜ[A] e.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A)))) := by
  rw [chain_comp_apply, complexLeftUnitor_inv_apply, tensorMap_apply,
    chain_comp_apply, complexRightUnitor_inv_apply, tensorMap_apply]
  rfl

end SerrePositivity.DifferentialGraded
