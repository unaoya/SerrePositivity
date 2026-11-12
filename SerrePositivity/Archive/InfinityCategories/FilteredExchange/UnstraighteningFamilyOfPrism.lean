module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningFamilyWitness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningSourceFamilyComparison

/-!
概要：任意の全パラメータの実 pointed prism から、同じ始点・終点の実現証拠を回収する。
方針：元の終点を標的の unstraightening の引き戻しへ入れ、既存の指定比較を適用する。
規約：元の prism を選び直さない。使われ方：第零面の可変初期値と第一辺の指定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
  (t : K ⟶ leftUnstraighteningTransformationSpace F G)
  (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hp : W ≫ pointedSpaceProjection = ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) ≫
    functorParameterizedPrism (intervalMappingUncurry t))

include hp in
/-- 元の prism の終点と底の射影は、元の標的図式上で厳密に可換する。 -/
lemma unstraighteningFamilyPrismEndpoint_base :
    ((prismEndpoint 1 (leftUnstraightening F) ▷ K) ≫ W) ≫ pointedSpaceProjection =
      (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) ≫ G := by
  rw [Category.assoc, hp, ← Category.assoc]
  change ((simplexPrismVertex 1 1 (leftUnstraightening F) ▷ K) ≫
    ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K)) ≫
      functorParameterizedPrism (intervalMappingUncurry t) = _
  rw [simplexPrismVertex_parameterizedBaseChange]
  rw [functorParameterizedPrism_vertex_of_const 1 _ 1 G (intervalMappingUncurry_one t),
    whiskerRight_fst_assoc, Category.assoc]

/-- 全族の実際の終点を、同じ底を持つ標的の全空間へ戻す。 -/
def unstraighteningFamilyPrismEndpoint :
    leftUnstraightening F ⊗ K ⟶ leftUnstraightening G :=
  pullback.lift ((prismEndpoint 1 (leftUnstraightening F) ▷ K) ≫ W)
    (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
    (unstraighteningFamilyPrismEndpoint_base F G t W hp)

/-- 回収した終点は元の底の射影を厳密に保持する。 -/
lemma unstraighteningFamilyPrismEndpoint_projection :
    unstraighteningFamilyPrismEndpoint F G t W hp ≫ leftUnstraighteningProjection G =
      fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F :=
  pullback.lift_snd _ _ _

variable (h₀ : (prismEndpoint 0 (leftUnstraightening F) ▷ K) ≫ W =
  fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F)

/-- 元の全 prism とそのままの実終点による、元の変換族の実現証拠。 -/
def unstraighteningFamilyOfPrism :
    UnstraighteningFamilyWitness F G t (unstraighteningFamilyPrismEndpoint F G t W hp) where
  prism := W
  source := h₀
  target := (pullback.lift_fst _ _ _).symm
  projection := hp

/-- 元の全 prism の実終点への比較は、既存の同じ指定始域比較そのもの。 -/
def unstraighteningFamilyOfPrism_comparison :
    FunctorIso ((t ≫ leftUnstraighteningMappingSpaceMap F G) ≫
      relativeFunctorOverPre (leftUnstraighteningProjection G)
        (Over.homMk (U := Over.mk (leftUnstraighteningProjection F))
          (V := Over.mk (leftUnstraighteningProjection F)) (𝟙 _) (Category.id_comp _)))
      (relativeFunctorCurry (unstraighteningFamilyPrismEndpoint F G t W hp)
        (unstraighteningFamilyPrismEndpoint_projection F G t W hp)) :=
  unstraighteningSourceFamilyComparisonIso F G (leftUnstraighteningProjection F)
    (𝟙 _) (Category.id_comp _) t (unstraighteningFamilyPrismEndpoint F G t W hp)
    (unstraighteningFamilyPrismEndpoint_projection F G t W hp) W
    (by simpa only [Category.id_comp] using h₀) (pullback.lift_fst _ _ _).symm hp

end SerrePositivity.InfinityCategories.F2
