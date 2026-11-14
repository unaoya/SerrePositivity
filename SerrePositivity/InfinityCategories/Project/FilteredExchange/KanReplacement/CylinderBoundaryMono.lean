module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderJointEndpoint

/-!
概要：通常の円柱の両端の直和から円柱への射は単射。
方針：同じ端では第一射影、異なる端では区間の値で区別する。
規約：形状の有限性や非空性は不要。
使われ方：指定された有限ホモトピーの両端を単射な境界として扱う。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：通常の円柱の両端を一つの境界射にまとめる。
方針：両端の直和の指定射。規約：始点が左。使われ方：単射な相対因子分解。 -/
def cylinderBoundaryInclusion (K : SSet.{u}) : K ⨿ K ⟶ K ⊗ (Δ[1] : SSet.{u}) :=
  coprod.desc SSet.ι₀ SSet.ι₁

/-- 概要：円柱の両端の包含は単射。
方針：各次数の直和の共同全射性で四通りを検査する。
規約：全形状。使われ方：Kan 標的への有限ホモトピーの境界固定近似。 -/
instance cylinderBoundaryInclusion_mono (K : SSet.{u}) : Mono (cylinderBoundaryInclusion K) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (mono_iff_injective _).2
  intro x y h
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sset_coprod_jointly_surjective K K n x <;>
    obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sset_coprod_jointly_surjective K K n y
  · have hh : (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})).app n a = SSet.ι₀.app n b := by
      simpa only [cylinderBoundaryInclusion, ← NatTrans.comp_app_apply, coprod.inl_desc] using h
    have hab : a = b := congrArg Prod.fst hh
    subst b
    rfl
  · have hh : (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})).app n a = SSet.ι₁.app n b := by
      simpa only [cylinderBoundaryInclusion, ← NatTrans.comp_app_apply,
        coprod.inl_desc, coprod.inr_desc] using h
    have he := congrArg (fun z : (K ⊗ (Δ[1] : SSet.{u})).obj n ↦
      (stdSimplex.objEquiv z.2).toOrderHom 0) hh
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) he)
  · have hh : (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})).app n a = SSet.ι₀.app n b := by
      simpa only [cylinderBoundaryInclusion, ← NatTrans.comp_app_apply,
        coprod.inl_desc, coprod.inr_desc] using h
    have he := congrArg (fun z : (K ⊗ (Δ[1] : SSet.{u})).obj n ↦
      (stdSimplex.objEquiv z.2).toOrderHom 0) hh
    exact False.elim ((by decide : (1 : Fin 2) ≠ 0) he)
  · have hh : (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})).app n a = SSet.ι₁.app n b := by
      simpa only [cylinderBoundaryInclusion, ← NatTrans.comp_app_apply, coprod.inr_desc] using h
    have hab : a = b := congrArg Prod.fst hh
    subst b
    rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
