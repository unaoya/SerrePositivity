module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningFamilyWitness

/-!
概要：元の unstraightening の全証拠の左結合表示から、元の両端の実作用を回収する。
方針：同じ結合子の逆と区間端点の厳密な式を使う。
規約：全係数と元の prism を保持。使われ方：定値三角形の長辺輸送の終点の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  {t : K ⟶ leftUnstraighteningTransformationSpace F G}
  {f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G}
  (w : UnstraighteningFamilyWitness F G t f)

/-- 左結合表示の元の始点も、元の全始点族の第一射影そのもの。 -/
lemma unstraighteningFamilyWitness_leftPrism_source :
    prismEndpoint 0 (leftUnstraightening F ⊗ K) ≫ w.leftPrism =
      fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F := by
  rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc,
    prismEndpoint_associator_inv, w.source]

/-- 左結合表示の元の終点も、元の全作用の第一射影そのもの。 -/
lemma unstraighteningFamilyWitness_leftPrism_target :
    prismEndpoint 1 (leftUnstraightening F ⊗ K) ≫ w.leftPrism =
      f ≫ pullback.fst pointedSpaceProjection G := by
  rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc,
    prismEndpoint_associator_inv, w.target]

end SerrePositivity.InfinityCategories.F2
