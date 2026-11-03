module

public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalObjects

/-!
概要：局所性を全単体集合パラメータの定値関手間 Hom で特徴づける。
方針：区間写像空間自身をパラメータに取り、同じ前合成の両側のホモトピー逆を回収する。
規約：パラメータの quasicategory 性は不要。使われ方：HTT 5.5.4 の余極限での閉性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 局所性は任意の単体集合パラメータの定値 Hom の前合成の全単射性と同値。 -/
lemma isLocalForHom_iff_constantHom_bijective {x y z : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    IsLocalForHom f z ↔ ∀ A : SSet.{u}, Function.Bijective
      (fun α : ConstantFunctorHom A X y z ↦ constantFunctorHomMap A f ≫ α) := by
  constructor
  · intro hf A
    exact isLocalForHom_constantHom_bijective f hf A
  · intro h
    apply (isLocalForHom_iff_interval f z).mpr
    let A := intervalMappingSpace y z
    let B := intervalMappingSpace x z
    let q := intervalPrecompose z f
    obtain ⟨α, hα⟩ := (h B).2 (intervalFamilyHom (𝟙 B))
    obtain ⟨g, rfl⟩ := intervalFamilyHom_surjective B X y z α
    have hg : intervalFamilyHom (g ≫ q) = intervalFamilyHom (𝟙 B) :=
      (intervalPrecompose_family f g).trans hα
    have hqg : intervalFamilyHom (q ≫ g) = intervalFamilyHom (𝟙 A) := by
      apply (h A).1
      change constantFunctorHomMap A f ≫ intervalFamilyHom (q ≫ g) =
        constantFunctorHomMap A f ≫ intervalFamilyHom (𝟙 A)
      rw [← intervalPrecompose_family, ← intervalPrecompose_family]
      have he := congrArg (intervalFamilyHomPrecomp q) hg
      rw [← intervalFamilyHom_precomp, ← intervalFamilyHom_precomp] at he
      dsimp only [q, A, B] at he ⊢
      simpa only [Category.assoc, Category.comp_id, Category.id_comp] using he
    have heq : IsSimplicialHomotopyEquivalence q :=
      ⟨g, intervalFamilyHom_eq_iff_homotopy.mp hqg, intervalFamilyHom_eq_iff_homotopy.mp hg⟩
    exact heq.isQCatEquivalence

end
end SerrePositivity.InfinityCategories.HomotopyLimits
