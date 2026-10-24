module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomPinchedGeneral
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomEvaluation
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapComposition
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedPrecomposition

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A]

/-- 閉前合成による評価は、その元の全次数の前合成射を回収する。 -/
lemma dgWalkingHomPinched_precomposition (D : Type v) [DGCategory A D] [Small.{u} D]
    {p q y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    dgWalkingHomPinched A D q y ≫
      pinchedHomChainMap ((dgWalkingHomEvaluation A D (homObject A D q y) p y
        (dgClosedPrecomposition A D r)).map
          (dgWalkingHomSource A (homObject A D q y))
          (dgWalkingHomTarget A (homObject A D q y))) =
      pinchedClosedPrecomposition A D r :=
  dgWalkingHomPinched_evaluation A D D q y p y (dgClosedPrecomposition A D r)

end SerrePositivity.InfinityCategories
