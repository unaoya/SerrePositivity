module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FatConeParameterPrism

/-!
概要：両端固定の fat 錐の全族を、固定頂点の関手空間へ curry する。
方針：内部 Hom の curry の後、両端の直和上の固定条件を fiber に添える。
規約：任意の右パラメータと元の全図式を厳密に保持する。
使われ方：定値始域の変換から錐への逆比較。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

variable {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 同じ指定頂点と図式を持つ fat 錐の全族を、固定頂点の空間へ戻す。 -/
def fixedFatConeFamilyCurry (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[0] K ⊗ T ⟶ X)
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K ▷ T) ≫ G = SSet.const z)
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K ▷ T) ≫ G = fst K T ≫ f) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace f z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (curry G) (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨s, t⟩
    cases s with
    | inl d =>
      change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K ▷ T) ≫ G).app n (d, t)) =
        (fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm z).app n (d, t)
      rw [h₀, SSet.yonedaEquiv_symm_zero, SSet.comp_const]
    | inr k =>
      change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K ▷ T) ≫ G).app n (k, t)) =
        (fst K T ≫ f).app n (k, t)
      rw [h₁])

/-- 同じ全族を curry した後に評価すると、元の全図式を厳密に回収する。 -/
lemma fixedFatConeFamilyCurry_uncurry (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[0] K ⊗ T ⟶ X)
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K ▷ T) ≫ G = SSet.const z)
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K ▷ T) ≫ G = fst K T ≫ f) :
    uncurry (fixedFatConeFamilyCurry G h₀ h₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fixedFatConeFamilyEvaluation f z) = G := by
  rw [fixedFatConeFamilyCurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fixedFatConeFamilyEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, uncurry_curry]

/-- 同じ全族を curry した後の元の円柱は、元の全図式への同じ制限。 -/
lemma fixedFatConeFamilyCurry_prism (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[0] K ⊗ T ⟶ X)
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K ▷ T) ≫ G = SSet.const z)
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K ▷ T) ≫ G = fst K T ≫ f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeParameterPrism (fixedFatConeFamilyCurry G h₀ h₁) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap K ▷ T) ≫ G := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeParameterPrism, fixedFatConeFamilyCurry_uncurry]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
