module
public import SerrePositivity.KST.NonConnective.DGKappaSplitNativeSquare
public import SerrePositivity.KST.NonConnective.DGKappaPerfZeroFamily
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CommutativeSquareRealization

/-!
概要：元の閉 dg 関手の分裂四角形の二胞体と、Perf の実零角を回収する。
方針：正方形の貼り合わせの制限を元の二単体で評価する。
規約：点ごとの cofiber 性はこの座標計算からは主張しない。
使われ方：実分裂 cofiber 族への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)

/-- 元の分裂四角形の上二単体は、零自己関手を経由する指定二単体。 -/
theorem dgKappaSplitClosedSquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ dgKappaSplitClosedSquare R D I Z =
      SSet.yonedaEquiv.symm (dgKappaSplitClosedUpper R D I Z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 元の分裂四角形の下二単体は、同じ注入と射影の指定二単体。 -/
theorem dgKappaSplitClosedSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgKappaSplitClosedSquare R D I Z =
      SSet.yonedaEquiv.symm (dgKappaSplitClosedLower R D I) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 同じ指定上二胞体を全 Perf 関手空間で厳密に回収する。 -/
theorem dgKappaSplitPerfFamilySquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ dgKappaSplitPerfFamilySquare R D I Z =
      SSet.yonedaEquiv.symm (dgKappaSplitClosedUpper R D I Z) ≫
        dgKappaClosedFunctorNativeMap R D I ≫ dgKappaFullPerfFamilyMap R D I := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ ((dgKappaSplitClosedSquare R D I Z ≫ _) ≫ _) = _
  rw [← Category.assoc, ← Category.assoc, dgKappaSplitClosedSquare_upper,
    Category.assoc]

/-- 同じ指定下二胞体を全 Perf 関手空間で厳密に回収する。 -/
theorem dgKappaSplitPerfFamilySquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgKappaSplitPerfFamilySquare R D I Z =
      SSet.yonedaEquiv.symm (dgKappaSplitClosedLower R D I) ≫
        dgKappaClosedFunctorNativeMap R D I ≫ dgKappaFullPerfFamilyMap R D I := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ ((dgKappaSplitClosedSquare R D I Z ≫ _) ≫ _) = _
  rw [← Category.assoc, ← Category.assoc, dgKappaSplitClosedSquare_lower,
    Category.assoc]

/-- 元の bottom 辺は、同じ実左注入の全 native Perf 像。 -/
theorem dgKappaSplitPerfFamilySquare_bottom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgKappaSplitPerfFamilySquare R D I Z =
      stdSimplex.δ (2 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgKappaSplitClosedLower R D I) ≫
          dgKappaClosedFunctorNativeMap R D I ≫ dgKappaFullPerfFamilyMap R D I := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge, Category.assoc,
    dgKappaSplitPerfFamilySquare_lower]

/-- 元の right 辺は、同じ実右射影の全 native Perf 像。 -/
theorem dgKappaSplitPerfFamilySquare_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgKappaSplitPerfFamilySquare R D I Z =
      stdSimplex.δ (0 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgKappaSplitClosedLower R D I) ≫
          dgKappaClosedFunctorNativeMap R D I ≫ dgKappaFullPerfFamilyMap R D I := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc,
    dgKappaSplitPerfFamilySquare_lower]

/-- 元の left 辺は、零自己関手への実零射の全 native Perf 像。 -/
theorem dgKappaSplitPerfFamilySquare_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgKappaSplitPerfFamilySquare R D I Z =
      stdSimplex.δ (2 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgKappaSplitClosedUpper R D I Z) ≫
          dgKappaClosedFunctorNativeMap R D I ≫ dgKappaFullPerfFamilyMap R D I := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge, Category.assoc,
    dgKappaSplitPerfFamilySquare_upper]

/-- 元の top 辺は、零自己関手からの実零射の全 native Perf 像。 -/
theorem dgKappaSplitPerfFamilySquare_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgKappaSplitPerfFamilySquare R D I Z =
      stdSimplex.δ (0 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgKappaSplitClosedUpper R D I Z) ≫
          dgKappaClosedFunctorNativeMap R D I ≫ dgKappaFullPerfFamilyMap R D I := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge, Category.assoc,
    dgKappaSplitPerfFamilySquare_upper]

/-- 同じ四角形の零角は、元の実零自己関手の全 Perf 作用の頂点。 -/
theorem dgKappaSplitPerfFamilySquare_corner :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaSplitPerfFamilySquare R D I Z) 0 1 =
      (dgKappaFullPerfFamilyMap R D I).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (dgKappaZeroFunctor R D I Z))) := by
  have hv := congrArg (fun F => F.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 3)))
      (dgKappaSplitPerfFamilySquare_upper R D I Z)
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaSplitPerfFamilySquare R D I Z) 0 1 =
    (dgKappaFullPerfFamilyMap R D I).app (Opposite.op ⦋0⦌) _ at hv
  refine hv.trans (congrArg ((dgKappaFullPerfFamilyMap R D I).app (Opposite.op ⦋0⦌)) ?_)
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- 元の実分裂四角形の同じ零角は、全 Perf 関手空間の零頂点。 -/
theorem dgKappaSplitPerfFamilySquare_corner_isZero :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaSplitPerfFamilySquare R D I Z) 0 1) := by
  rw [dgKappaSplitPerfFamilySquare_corner]
  exact dgKappaFullPerfZeroVertex_isZero R D I Z

/-- 元の全 Perf 関手空間における、同じ零角を持つ実三角形。 -/
def dgKappaSplitPerfZeroTriangle : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)))) where
  square := dgKappaSplitPerfFamilySquare R D I Z
  zero_corner := dgKappaSplitPerfFamilySquare_corner_isZero R D I Z

end SerrePositivity.KST.NonConnective
