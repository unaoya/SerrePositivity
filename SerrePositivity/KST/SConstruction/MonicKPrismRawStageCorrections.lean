module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeRawComparison
public import SerrePositivity.KST.SConstruction.RawComparisonRectificationCorrections

/-! # 元の K 合成比較の全段に保存した累積相対補正
概要：元の各段比較から同じ全 raw 円柱の評価への実二次元補正を具体化する。
方針：元の全適合比較と累積補正をそのまま使い、全区間境界の固定を回収する。
規約：正の全段で元の補正全体を保持し、零段は元の定数円柱そのもの。
使われ方：元の BF 合成比較の段評価を、元の各段 span 三角形へ結び付ける。
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

/-- 元の各段比較から同じ全 raw 円柱の評価への、元の累積補正円柱全体。 -/
def monicKPrismNativeRawStageCorrection (n : ℕ) :=
  rawComparisonRectificationCorrection (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z))
    (nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g))
    (compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g)
    (monicKPrismNativeLevelComparison F f g) (monicKPrismNativeRawCompatibility F f g)
    (monicKPrismNativeRawCompatibility_boundary F f g) n

/-- 元の全二次元補正は、同じ累積段に保存した全実円柱そのもの。 -/
lemma monicKPrismNativeRawStageCorrection_h (n : ℕ) :
    (monicKPrismNativeRawStageCorrection F f g n).h =
      (monicKPrismNativeCumulativeComparisonStage F f g n).correction.h :=
  rawComparisonRectificationCorrection_h _ _ _ _ _ _ _ n

/-- 全段の元の区間境界は、元の全補正の全時刻で厳密に固定する。 -/
lemma monicKPrismNativeRawStageCorrection_boundary (n : ℕ) :
    ((nerve (CompositionStringParameters f g) ◁ (SSet.boundary 1).ι) ▷
        (Δ[1] : SSet.{u})) ≫ (monicKPrismNativeRawStageCorrection F f g n).h =
      fst (nerve (CompositionStringParameters f g) ⊗ (∂Δ[1] : SSet.{u})) Δ[1] ≫
        (nerve (CompositionStringParameters f g) ◁ (SSet.boundary 1).ι) ≫
          (monicKPrismNativeLevelComparison F f g n).h :=
  rawComparisonRectificationCorrection_boundary _ _ _ _ _ _ _ n

/-- 零段の補正全体は、元の零段比較を全時刻固定する同じ定数円柱。 -/
lemma monicKPrismNativeRawStageCorrection_zero :
    (monicKPrismNativeRawStageCorrection F f g 0).h =
      fst (nerve (CompositionStringParameters f g) ⊗ (Δ[1] : SSet.{u})) Δ[1] ≫
        (monicKPrismNativeLevelComparison F f g 0).h :=
  rawComparisonRectificationCorrection_zero _ _ _ _ _ _ _

end SerrePositivity.KST.SConstruction
