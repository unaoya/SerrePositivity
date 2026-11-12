module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeComparisonCompatibility
public import SerrePositivity.KST.SConstruction.RawComparisonRectification

/-! # 元の全精密化上の直接厳密化と BF 合成の全段 raw 比較
概要：元の四三角形による全適合比較と累積相対補正から、一つの全段 raw 円柱を構成する。
方針：各段比較・元の全境界固定適合を累積帰納へ渡し、同じ全評価を厳密に束ねる。
規約：二つの元の raw 族を両端に保ち、零段は全時刻で元の定数円柱。
使われ方：指定した BF 境界を持つ相対延長と coherent な合成面の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の全適合比較を、同じ全円柱の射影と構造射像の間に表示する。 -/
def monicKPrismNativeRawCompatibility (n : ℕ) : SSet.Homotopy
    ((monicKPrismNativeLevelComparison F f g (n + 1)).h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj z)).level (n + 1)).space)
    ((monicKPrismNativeLevelComparison F f g n).h ≫
      RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) :=
  familyHomotopyEndpointTransport (monicKPrismNativeComparisonCompatibility F f g n) rfl
    (monicKPrismNativePreviousComparison_h F f g n)

/-- 表示の移送でも元の全二次元比較を厳密に保持する。 -/
lemma monicKPrismNativeRawCompatibility_h (n : ℕ) :
    (monicKPrismNativeRawCompatibility F f g n).h =
      (monicKPrismNativeComparisonCompatibility F f g n).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 元の全区間境界は、全適合比較の全時刻を通して厳密に固定される。 -/
lemma monicKPrismNativeRawCompatibility_boundary (n : ℕ) :
    ((nerve (CompositionStringParameters f g) ◁ (SSet.boundary 1).ι) ▷
        (Δ[1] : SSet.{u})) ≫ (monicKPrismNativeRawCompatibility F f g n).h =
      fst (nerve (CompositionStringParameters f g) ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫
        (nerve (CompositionStringParameters f g) ◁ (SSet.boundary 1).ι) ≫
        (monicKPrismNativeLevelComparison F f g (n + 1)).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space := by
  rw [monicKPrismNativeRawCompatibility_h]
  exact familyCylinder_fixed_boundary
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (monicKPrismNativeLevelComparison F f g (n + 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj z)).level (n + 1)).space))
    (monicKPrismNativeComparisonCompatibility_source F f g n)
    (monicKPrismNativeComparisonCompatibility_target F f g n)

/-- 元の各段比較と全境界固定適合からの累積補正済みの同じ各段データ。 -/
def monicKPrismNativeCumulativeComparisonStage (n : ℕ) :=
  rawComparisonStage (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z))
    (nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g))
    (compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g)
    (monicKPrismNativeLevelComparison F f g) (monicKPrismNativeRawCompatibility F f g)
    (monicKPrismNativeRawCompatibility_boundary F f g) n

/-- 元の二つの全 raw 族を両端に持つ、累積補正を反映した全段の実円柱。 -/
def monicKPrismNativeRawComparison : SSet.Homotopy
    (nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g))
    (compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g) :=
  rawComparisonRectification (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z))
    _ _ (monicKPrismNativeLevelComparison F f g) (monicKPrismNativeRawCompatibility F f g)
    (monicKPrismNativeRawCompatibility_boundary F f g)

/-- 全円柱の各段は、同じ累積補正済みの段円柱そのもの。 -/
lemma monicKPrismNativeRawComparison_evaluation (n : ℕ) :
    (monicKPrismNativeRawComparison F f g).h ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n =
      (monicKPrismNativeCumulativeComparisonStage F f g n).val.h :=
  rawComparisonRectificationMap_evaluation _ _ _ _ _ _ _ n

/-- 零段の全円柱は元の合成射で全時刻固定される。 -/
lemma monicKPrismNativeRawComparison_zero :
    (monicKPrismNativeRawComparison F f g).h ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) 0 =
      fst (nerve (CompositionStringParameters f g)) (Δ[1] : SSet.{u}) ≫
        SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) :=
  (rawComparisonRectification_zero _ _ _ _ _ _ _).trans
    (monicKPrismNativeLevelComparison_zero F f g)

end SerrePositivity.KST.SConstruction
