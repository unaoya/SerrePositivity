module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion
public import SerrePositivity.InfinityCategories.HTT.Section1_2_9.OverIso
public import Mathlib.CategoryTheory.Category.ULift

/-! # 閉零圏の厳密 over nerve から dg nerve の実 over slice へ

概要：対象と Hom を共通宇宙へ持ち上げ、通常の over nerve の比較を実 dg slice へ送る。
方針：AsSmall、F1B の通常の over 比較、閉 nerve 包含、固定終点の等式輸送を使う。
規約：元の対象と Hom の独立宇宙を保つ。同値性・cofinality は主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 閉零圏の対象・Hom を共通宇宙に置いた通常の圏。 -/
abbrev DGCommonClosedCategory := AsSmall.{max u v} (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D)

/-- 独立な Hom 宇宙を持つ通常の nerve 間で、共通宇宙の閉圏から戻す。 -/
def dgCommonClosedNerveDown : nerve (DGCommonClosedCategory A D) ⟶ nerve (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D) where
  app _ := ↾fun σ => σ ⋙ (AsSmall.down : DGCommonClosedCategory A D ⥤ _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D)

/-- 元の厳密 over nerve を、共通宇宙の over nerve へ送る。 -/
def dgClosedNerveOverUp (x : D) : nerve (Over (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) ⟶
    nerve (Over ((AsSmall.up : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D ⥤ DGCommonClosedCategory A D).obj
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x))) where
  app _ := ↾fun σ => σ ⋙ Over.post
    (AsSmall.up : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D ⥤ DGCommonClosedCategory A D)

/-- 共通宇宙の通常の閉 nerve を元の実 dg nerve へ送る。 -/
def dgCommonClosedNerveToDG : nerve (DGCommonClosedCategory A D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  dgCommonClosedNerveDown A D ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A D

/-- 共通宇宙から戻した指定終点は、元の実 dg 頂点に厳密に一致。 -/
lemma dgCommonClosedNervePoint (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint ((AsSmall.up : ClosedCategory A D ⥤ DGCommonClosedCategory A D).obj
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) ≫ dgCommonClosedNerveToDG A D =
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) := by
  apply SSet.yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A D).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ForgetEnrichment.of (Complex A) x)) = _
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D).injective
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_vertex]
  rfl

/-- 閉零圏の通常の厳密 over nerve から、元の指定頂点上の実 over slice への比較。 -/
def dgClosedNerveOverMap (x : D) :
    nerve (Over (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) :=
  dgClosedNerveOverUp A D x ≫
  (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso ((AsSmall.up : ClosedCategory A D ⥤ DGCommonClosedCategory A D).obj
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x))).hom ≫
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint ((AsSmall.up : ClosedCategory A D ⥤ DGCommonClosedCategory A D).obj
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x))) (dgCommonClosedNerveToDG A D) ≫
  (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (dgCommonClosedNervePoint A D x))).hom

/-- Hom 宇宙を変えずに、元の厳密 over nerve の始域を取り出す。 -/
def dgClosedNerveOverSourceMap (x : D) :
    nerve (Over (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) ⟶ nerve (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D) where
  app _ := ↾fun σ => σ ⋙ Over.forget (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)

/-- 厳密 over nerve の比較は、元の始域への実 dg nerve 射影を厳密に保つ。 -/
lemma dgClosedNerveOverMap_projection (x : D) :
    dgClosedNerveOverMap A D x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) =
        dgClosedNerveOverSourceMap A D x ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A D := by
  dsimp only [dgClosedNerveOverMap]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverProjection_eqTransport, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso _).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _)
      (dgCommonClosedNerveToDG A D), _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso_projection]
    rfl
  · exact dgCommonClosedNervePoint A D x

end SerrePositivity.InfinityCategories.Project.DerivedCategories
