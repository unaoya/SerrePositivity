module
public import SerrePositivity.DifferentialGraded.Complexes.ConeComposition

/-! # 合成coneの逆方向比較に用いるdescの境界式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L P : Complex A}

lemma complexConeComp_inner_boundary (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) :
    δ (-1) 0 ((Cochain.ofHom f).comp (mappingCone.inl g) (zero_add (-1))) =
      Cochain.ofHom (θ ≫ mappingCone.inr g) := by
  subst θ
  rw [δ_ofHom_comp, mappingCone.δ_inl, ← Cochain.ofHom_comp, Category.assoc]

lemma complexConeComp_outer_boundary (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    δ (-1) 0 ((mappingCone.snd f).comp (mappingCone.inl g) (zero_add (-1))) =
      Cochain.ofHom (χ ≫ mappingCone.desc θ
        ((Cochain.ofHom f).comp (mappingCone.inl g) (zero_add (-1))) (mappingCone.inr g)
        (complexConeComp_inner_boundary f g θ hθ)) := by
  subst θ
  subst χ
  apply Cochain.ext₀
  intro p
  rw [mappingCone.ext_from_iff _ (p + 1) p rfl,
    mappingCone.ext_to_iff _ _ (p + 1) rfl]
  simp [mappingCone.map, δ_zero_cochain_comp,
    Cochain.comp_v _ _ (add_neg_cancel 1) p (p + 1) p (by omega) (by omega)]

end SerrePositivity.DifferentialGraded
