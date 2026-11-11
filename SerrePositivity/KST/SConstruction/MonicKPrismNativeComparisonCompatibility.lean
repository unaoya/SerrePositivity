module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeComparisonImages
public import SerrePositivity.KST.SConstruction.FourTriangleComparison
public import SerrePositivity.KST.SConstruction.FamilyCylinderTriangleComparison

/-! # 元の各段比較円柱の構造適合の端点固定実二次元比較
概要：二組の構造三角形と元の前後段 span 三角形の実像から、比較円柱の適合を得る。
方針：同じ四つの全三角形で共通辺を消去し、実比較三角形と正方形を復号する。
規約：元の各段円柱の射影・構造射像を全体として両面に保ち、両端を全時刻固定する。
使われ方：単射源の写像空間制限に沿う両端固定の逐次持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の四三角形から内部構成した、次段射影と前段構造射像の実比較三角形。 -/
def monicKPrismNativeComparisonCompatibilityTriangle (n : ℕ) :=
  fourTriangleComparisonTriangle
    (monicKPrismNativeDirectStructureTriangle F f g n)
    (monicKPrismNativeStructureTriangle F f g n)
    (monicKPrismNativePreviousComparisonTriangle F f g n)
    (monicKPrismNativeProjectedComparisonTriangle F f g n)

/-- 元の各段比較円柱の射影と構造射像を結ぶ、両端固定の実二次元比較。 -/
def monicKPrismNativeComparisonCompatibility (n : ℕ) : SSet.Homotopy
    (monicKPrismNativeProjectedComparison F f g n).h
    (monicKPrismNativePreviousComparison F f g n).h :=
  familyCylinderTriangleComparison (monicKPrismNativeComparisonCompatibilityTriangle F f g n)

/-- 零面は保存済み次段比較円柱全体の元の源構造射への制限。 -/
lemma monicKPrismNativeComparisonCompatibility_zero (n : ℕ) :
    SSet.ι₀ ≫ (monicKPrismNativeComparisonCompatibility F f g n).h =
      (monicKPrismNativeLevelComparison F f g (n + 1)).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space :=
  (monicKPrismNativeComparisonCompatibility F f g n).h₀

/-- 一面は保存済み前段比較円柱全体の元の構造射像。 -/
lemma monicKPrismNativeComparisonCompatibility_one (n : ℕ) :
    SSet.ι₁ ≫ (monicKPrismNativeComparisonCompatibility F f g n).h =
      (monicKPrismNativeLevelComparison F f g n).h ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n :=
  (monicKPrismNativeComparisonCompatibility F f g n).h₁.trans
    (monicKPrismNativePreviousComparison_h F f g n)

/-- 直接厳密化側の raw 評価は全比較時刻で同じ元の始点に固定する。 -/
lemma monicKPrismNativeComparisonCompatibility_source (n : ℕ) :
    (SSet.ι₀ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeComparisonCompatibility F f g n).h =
      fst (nerve (CompositionStringParameters f g)) (Δ[1] : SSet.{u}) ≫
        (nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z))
            (n + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
              ((kKanSequence (F.obj z)).level (n + 1)).space :=
  familyCylinderTriangleComparison_source _

/-- BF 合成側の raw 評価も全比較時刻で同じ元の終点に固定する。 -/
lemma monicKPrismNativeComparisonCompatibility_target (n : ℕ) :
    (SSet.ι₁ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeComparisonCompatibility F f g n).h =
      fst (nerve (CompositionStringParameters f g)) (Δ[1] : SSet.{u}) ≫
        (compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z))
            (n + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
              ((kKanSequence (F.obj z)).level (n + 1)).space :=
  familyCylinderTriangleComparison_target _

end SerrePositivity.KST.SConstruction
