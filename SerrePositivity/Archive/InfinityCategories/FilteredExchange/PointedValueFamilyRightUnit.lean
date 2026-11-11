module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueFamilyFactorPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueRightTriangleReindex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：右 Hom で戻した点における元の始点単位因子を、同じ指定余単位の像へ同定する。
方針：元の第二三角恒等式を、元の二つの実端点表示へ値を保って移す。
規約：元の単位・余単位を保持。使われ方：余単位正方形から元の値比較への代入。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の右 Hom で戻した点の始点単位因子は、元の指定余単位の同じ右 Hom への像。 -/
lemma pointedValueFamilySourceUnitIso_at_right (K : KanObject.{u}) {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj) :
    pointedValueFamilySourceUnitIso K (x ≫ pointedRightFiberComparison K) =
      (pointedValueFamilyTargetCounitIso K x).postcomp (pointedRightFiberComparison K) := by
  let u := pointedValueRightComparison_unitIso (spaceInfinityVertex K)
  let c := (pointedValueRightComparison_counitIso (spaceInfinityVertex K)).precomp x
  have hU := pointedValueFamilySourceUnitIso_heq_unit K (x ≫ pointedRightFiberComparison K)
  have hC := pointedValueFamilyTargetCounitIso_heq_counit K x
  have hp := functorIso_postcomp_heq_of_heq c (pointedValueFamilyTargetCounitIso K x)
    (by simp only [pointedValueRightComparison_standard, Category.assoc])
    (Category.comp_id x) hC (pointedRightFiberComparison K)
  have hm : x ≫ pointedRightFiberComparison K =
      x ≫ pointedValueRightComparison (spaceInfinityVertex K) := by
    rw [pointedValueRightComparison_standard]
  have hpre := functorIso_precomp_heq_of_map_eq u hm
  have hpost := functorIso_postcomp_heq_of_map_eq c (pointedValueRightComparison_standard K)
  have htri := pointedValueRightComparison_triangle_inverse_at (spaceInfinityVertex K) x
  exact eq_of_heq (hU.trans (hpre.trans
    ((heq_of_eq htri).trans (hpost.symm.trans hp.symm))))

end SerrePositivity.InfinityCategories.F2
