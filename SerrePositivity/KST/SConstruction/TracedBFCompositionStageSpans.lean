module
public import SerrePositivity.KST.SConstruction.TracedBFCompositionStageCorrections
public import SerrePositivity.KST.SConstruction.PointParameterMaps

/-! # 元の全各段合成 span 三角形の同じ直通列制限
概要：元の各段 span 三角形全体を直通列点へ制限し、元の全三辺と補正始端を回収する。
方針：同じ全実三角形を一点パラメータで前合成し、三面の厳密な自然性を使う。
規約：正の全段で元の全二単体を保持する。新しい三角形を充填しない。
使われ方：元の全補正でこの比較面を実 BF 段評価へ移す、正の段の第四辺比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の全各段 span 三角形の同じ直通列点での全実像。 -/
def monicKTracedCompositionOriginalSpan (n : ℕ) :=
  pointParameterMap (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g)))
    (Δ[2] : SSet.{u}) ≫ monicKPrismNativeLevelComparisonMap F f g n

/-- 第一面は、元の直接厳密化補正円柱の同じ直通列制限全体。 -/
lemma monicKTracedCompositionOriginalSpan_first (n : ℕ) :
    stdSimplex.δ 2 ≫ monicKTracedCompositionOriginalSpan F f g n =
      monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeDirectCorrectionData F f g n).homotopy.h := by
  rw [monicKTracedCompositionOriginalSpan, ← Category.assoc, pointParameterMap_naturality,
    Category.assoc, monicKPrismNativeLevelComparisonMap_first]
  rfl

/-- 比較面は、元の全段補正の始端に保持した同じ補正前区間全体。 -/
lemma monicKTracedCompositionOriginalSpan_comparison (n : ℕ) :
    stdSimplex.δ 0 ≫ monicKTracedCompositionOriginalSpan F f g n =
      monicKTracedCompositionOriginalStage F f g n := by
  rw [monicKTracedCompositionOriginalSpan, ← Category.assoc, pointParameterMap_naturality,
    Category.assoc, monicKPrismNativeLevelComparisonMap_comparison]
  rfl

/-- 合成面も、元の BF 合成補正円柱の同じ直通列制限全体。 -/
lemma monicKTracedCompositionOriginalSpan_composite (n : ℕ) :
    stdSimplex.δ 1 ≫ monicKTracedCompositionOriginalSpan F f g n =
      monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeCompositeCorrectionData F f g n).homotopy.h := by
  rw [monicKTracedCompositionOriginalSpan, ← Category.assoc, pointParameterMap_naturality,
    Category.assoc, monicKPrismNativeLevelComparisonMap_composite]
  rfl

/-- 元の全比較面は、同じ累積補正の全始端として厳密に回収する。 -/
lemma monicKTracedCompositionStageCorrection_span_source (n : ℕ) :
    SSet.ι₀ ≫ (monicKTracedCompositionStageCorrection F f g n).h =
      stdSimplex.δ 0 ≫ monicKTracedCompositionOriginalSpan F f g n :=
  (monicKTracedCompositionStageCorrection_source F f g n).trans
    (monicKTracedCompositionOriginalSpan_comparison F f g n).symm

end SerrePositivity.KST.SConstruction
