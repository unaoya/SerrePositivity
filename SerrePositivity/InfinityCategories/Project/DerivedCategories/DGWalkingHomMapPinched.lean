module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapComposition

/-! # 自由 Hom の係数変換と全 pinched 単体

概要：自由係数の包含は、任意の係数鎖写像と全次数で可換。
方針：生成辺への作用を pinched Hom の合成則へ渡す。
規約：単体集合の射の等式。使われ方：商への自由係数 prism の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]
variable {q y : D} {q' y' : E}

/-- 生成辺の全 pinched 包含は係数鎖写像と厳密に可換。 -/
lemma dgWalkingHomMap_pinched
    (θ : homObject A D q y ⟶ homObject A E q' y') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator.{u, v} A (homObject A D q y)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap.{u, v} A θ).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y))) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap θ ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator.{u, v} A (homObject A E q' y')) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap_generator, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
