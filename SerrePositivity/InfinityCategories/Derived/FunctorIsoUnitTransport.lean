module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoInverseSourceComparison
/-!
概要：同じ全関手同型に沿い、指定単位の前後合成を移す。
方針：h Fun の実交換則と同じ比較の逆を使う。
規約：単位の値を変更しない。使われ方：graph と diagonal の導来単位比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIso_unit_target_transport {X Y : SSet.{u}}
    [Quasicategory Y] (A B : X ⟶ Y) (a : FunctorIso B A)
    (F : Y ⟶ Y) (u : FunctorIso F (𝟙 Y)) :
    FunctorIso.postcomp a.symm F ≪≫ u.precomp B ≪≫ a = u.precomp A := by
  have h := F2.functorIso_whisker_exchange a u
  simp only [F2.functorIso_postcomp_id] at h
  calc
    _ = FunctorIso.postcomp a.symm F ≪≫ (a.postcomp F ≪≫ u.precomp A) := by
      rw [← h]
    _ = _ := by
      simp only [F2.functorIso_postcomp_symm, Iso.symm_self_id_assoc]
lemma functorIso_unit_source_transport {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (A B : X ⟶ Y) (a : FunctorIso B A)
    (F : X ⟶ X) (u : FunctorIso F (𝟙 X)) :
    FunctorIso.precomp a.symm F ≪≫ u.postcomp B ≪≫ a = u.postcomp A := by
  have h := F2.functorIso_whisker_exchange u a
  simp only [functorIso_precomp_id] at h
  calc
    _ = FunctorIso.precomp a.symm F ≪≫ (a.precomp F ≪≫ u.postcomp A) := by
      rw [h]
    _ = _ := by
      simp only [F2.functorIso_precomp_symm, Iso.symm_self_id_assoc]
end
end SerrePositivity.InfinityCategories
