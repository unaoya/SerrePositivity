module
public import SerrePositivity.KST.SConstruction.RawComparisonRectification

/-! # 元の各段比較から全 raw 円柱の同じ段への全相対補正
概要：累積補正の各段に保存した同じ実二次元円柱を、最終 raw 評価との比較として回収する。
方針：各段評価の厳密な式で終端の表示だけを移し、元の全補正と全境界固定を保存する。
規約：元の段比較・補正円柱を選び直さない。零段の補正は元の定数円柱そのもの。
使われ方：BF 合成比較の全正段を、元の合成 span 三角形へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {U : SSet.{u}}
  (a b : U ⟶ RawSpectrumMapping.space X Y)
  (H : ∀ n, SSet.Homotopy (a ≫ RawSpectrumMapping.evaluation X Y n)
    (b ≫ RawSpectrumMapping.evaluation X Y n))
  (L : ∀ n, SSet.Homotopy
    ((H (n + 1)).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    ((H n).h ≫ RawSpectrumMapping.step X Y n))
  (hL : ∀ n, ((U ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫ (L n).h =
    fst (U ⊗ (∂Δ[1] : SSet.{u})) Δ[1] ≫ (U ◁ (SSet.boundary 1).ι) ≫
      (H (n + 1)).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)

/-- 元の各段比較から最終 raw 円柱の同じ段への、保存済みの同じ全補正。 -/
def rawComparisonRectificationCorrection (n : ℕ) : SSet.Homotopy (H n).h
    ((rawComparisonRectification X Y a b H L hL).h ≫ RawSpectrumMapping.evaluation X Y n) :=
  familyHomotopyEndpointTransport (rawComparisonStage X Y a b H L hL n).correction rfl
    (rawComparisonRectificationMap_evaluation X Y a b H L hL n).symm

/-- 終端の表示移送でも、元の同じ全二次元補正そのもの。 -/
lemma rawComparisonRectificationCorrection_h (n : ℕ) :
    (rawComparisonRectificationCorrection X Y a b H L hL n).h =
      (rawComparisonStage X Y a b H L hL n).correction.h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 元の全区間境界は、全段の補正の全時刻で厳密に固定される。 -/
lemma rawComparisonRectificationCorrection_boundary (n : ℕ) :
    ((U ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫
        (rawComparisonRectificationCorrection X Y a b H L hL n).h =
      fst (U ⊗ (∂Δ[1] : SSet.{u})) Δ[1] ≫ (U ◁ (SSet.boundary 1).ι) ≫ (H n).h := by
  rw [rawComparisonRectificationCorrection_h]
  exact (rawComparisonStage X Y a b H L hL n).boundary

/-- 零段の補正全体は、元の零段比較を全時刻固定する定数円柱。 -/
lemma rawComparisonRectificationCorrection_zero :
    (rawComparisonRectificationCorrection X Y a b H L hL 0).h =
      fst (U ⊗ (Δ[1] : SSet.{u})) Δ[1] ≫ (H 0).h := by
  rw [rawComparisonRectificationCorrection_h]
  rfl

end SerrePositivity.KST.SConstruction
