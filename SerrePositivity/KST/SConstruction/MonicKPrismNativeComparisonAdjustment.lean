module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeComparisonCompatibility
public import SerrePositivity.KST.SConstruction.FamilyCylinderEndpointAdjustment

/-! # 元の各段比較の両端を保つ実構造補正
概要：保存済み次段比較円柱を、前段比較の構造射像へ厳密に射影するよう相対補正する。
方針：単射な源構造射の写像空間制限に、四三角形からの全二次元比較を持ち上げる。
規約：二つの raw 評価を両端に厳密に保持し、全区間境界と元の基底比較全体を保つ。
使われ方：全段 raw 比較の逐次構成に用いる実相対持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

local instance nativeComparisonEndpointRestrictionFibration (n : ℕ) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
      ((kKanSequence (F.obj z)).level (n + 1)).space) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration _ _

/-- 元の全適合比較を持ち上げ、両端を保って次段比較の射影を厳密に補正する。 -/
def monicKPrismNativeComparisonAdjustmentData (n : ℕ) :=
  cylinderEndpointAdjustmentData
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
      ((kKanSequence (F.obj z)).level (n + 1)).space)
    (monicKPrismNativeLevelComparison F f g (n + 1))
    (monicKPrismNativePreviousComparison F f g n)
    (monicKPrismNativeComparisonCompatibility F f g n)
    (monicKPrismNativeComparisonCompatibility_source F f g n)
    (monicKPrismNativeComparisonCompatibility_target F f g n)

/-- 補正後の次段実比較は、元の前段比較の構造射像を厳密に回収する。 -/
lemma monicKPrismNativeComparisonAdjustmentData_projection (n : ℕ) :
    (monicKPrismNativeComparisonAdjustmentData F f g n).val.h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space =
      (monicKPrismNativeLevelComparison F f g n).h ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n :=
  (monicKPrismNativeComparisonAdjustmentData F f g n).projection.trans
    (monicKPrismNativePreviousComparison_h F f g n)

/-- 元の次段比較から補正後への全二次元比較は、区間境界全体を全時刻固定する。 -/
lemma monicKPrismNativeComparisonAdjustmentData_boundary (n : ℕ) :
    ((nerve (CompositionStringParameters f g) ◁ (SSet.boundary 1).ι) ▷
        (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeComparisonAdjustmentData F f g n).comparison.h =
      fst (nerve (CompositionStringParameters f g) ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫
        (nerve (CompositionStringParameters f g) ◁ (SSet.boundary 1).ι) ≫
          (monicKPrismNativeLevelComparison F f g (n + 1)).h :=
  (monicKPrismNativeComparisonAdjustmentData F f g n).boundary

/-- 全相対補正の射影は、四つの元の三角形から構成した同じ全二次元比較。 -/
lemma monicKPrismNativeComparisonAdjustmentData_comparison_projection (n : ℕ) :
    (monicKPrismNativeComparisonAdjustmentData F f g n).comparison.h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space =
      (monicKPrismNativeComparisonCompatibility F f g n).h :=
  (monicKPrismNativeComparisonAdjustmentData F f g n).comparison_projection

end SerrePositivity.KST.SConstruction
