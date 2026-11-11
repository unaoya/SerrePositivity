module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomPinchedGeneral
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedPrecomposition

/-! # 全次数の pinched Hom の自由係数表示

概要：自由 Hom の生成辺に全 pinched 単体を含め、評価による全次数の回収を証明する。
方針：生成辺の評価公式を pinched Hom 鎖写像の合成公式へ移す。
規約：頂点だけでなく単体集合の射の等式。使われ方：閉前合成 prism の両端の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A]

/-- 閉前合成による評価は、その元の全次数の前合成射を回収する。 -/
lemma dgWalkingHomPinched_precomposition (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
    {p q y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D (homObject A D q y) p y
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r)).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y))) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D r :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched_evaluation A D D q y p y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
