module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeStructureFaces
public import SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData

/-! # 直接厳密化と BF 合成の各段の実比較
概要：元の同じ合成射からの二つの保存済み円柱を使い、二つの raw 評価を実比較する。
方針：元の二列を実 span 三角形で比較し、零段では元の定数円柱を保持する。
規約：全補正列の証人と元の二円柱全体を保持し、零段に余分な区間を追加しない。
使われ方：二組の構造適合三角形と合わせた全段 raw 比較の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 同じ元の始点からの保存済み二円柱を二面に持つ実比較データ。 -/
def monicKPrismNativeLevelComparisonData (n : ℕ) : FamilyCorrectionSpanData
    (monicKPrismNativeDirectCorrectionData F f g n).homotopy
    (monicKPrismNativeCompositeCorrectionData F f g n).homotopy :=
  match n with
  | 0 => familyCorrectionSpanDataOfEmpty
      (monicKPrismNativeDirectCorrectionChain F f g 0)
      (monicKPrismNativeCompositeCorrectionChain F f g 0)
      (monicKPrismNativeDirectCorrectionChain_zero_trace F f g)
      (monicKPrismNativeCompositeCorrectionChain_zero_trace F f g)
  | n + 1 => familyCorrectionSpanData (monicKPrismNativeDirectCorrectionChain F f g (n + 1))
      (monicKPrismNativeCompositeCorrectionChain F f g (n + 1))

/-- 各段の二つの raw 評価の間の実比較円柱。 -/
def monicKPrismNativeLevelComparison (n : ℕ) :=
  (monicKPrismNativeLevelComparisonData F f g n).homotopy

/-- 元の二円柱と各段の実比較円柱を全三面に持つ全パラメータの実三角形。 -/
def monicKPrismNativeLevelComparisonMap (n : ℕ) :=
  (monicKPrismNativeLevelComparisonData F f g n).realization

/-- 第一面は直接厳密化の保存済み円柱全体。 -/
lemma monicKPrismNativeLevelComparisonMap_first (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
        monicKPrismNativeLevelComparisonMap F f g n =
      (monicKPrismNativeDirectCorrectionData F f g n).homotopy.h :=
  (monicKPrismNativeLevelComparisonData F f g n).realization_first

/-- 第二面は二つの raw 評価の間の同じ実比較円柱。 -/
lemma monicKPrismNativeLevelComparisonMap_comparison (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 0) ≫
        monicKPrismNativeLevelComparisonMap F f g n =
      (monicKPrismNativeLevelComparison F f g n).h :=
  (monicKPrismNativeLevelComparisonData F f g n).realization_comparison

/-- 合成面は BF 合成の保存済み円柱全体。 -/
lemma monicKPrismNativeLevelComparisonMap_composite (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 1) ≫
        monicKPrismNativeLevelComparisonMap F f g n =
      (monicKPrismNativeCompositeCorrectionData F f g n).homotopy.h :=
  (monicKPrismNativeLevelComparisonData F f g n).realization_composite

/-- 零段では実比較の全時刻が同じ元の合成射に厳密に固定される。 -/
lemma monicKPrismNativeLevelComparison_zero :
    (monicKPrismNativeLevelComparison F f g 0).h =
      fst (nerve (CompositionStringParameters f g)) (Δ[1] : SSet.{u}) ≫
        SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) :=
  rfl

end SerrePositivity.KST.SConstruction
