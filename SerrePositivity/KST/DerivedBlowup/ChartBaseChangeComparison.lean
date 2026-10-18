module

public import SerrePositivity.KST.DerivedBlowup.KoszulConeComparison

/-!
概要：KST Def3.1 のチャート Koszul 複体を係数環の変更後の外積複体と比較する。
方針：既存 baseChangeKoszulIso と一般有限列の外積比較を生成元列挙で結ぶ。
規約：ここでは複体の項ごとのスカラー拡大。導来スカラー拡大との比較は別工程。
使われ方：共通重なり環上でのチャートの複体比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {r : ℕ}

/-- 概要：任意係数環上のチャート生成元の有限列挙同型。
方針：finSuccAboveEquiv を自由加群へ持ち上げる。
規約：KST Def3.1。使われ方：スカラー拡大後の外積模型の比較。 -/
def chartGeneratorEnumerationEquiv (i : Fin (r + 1)) :
    (Fin r →₀ B) ≃ₗ[B] (ChartIndex i →₀ B) :=
  Finsupp.domLCongr (finSuccAboveEquiv i)

/-- 概要：係数環変更後のチャート関係式の列挙は微分を保つ。
方針：単一生成元で関係式の環射による像を計算する。
規約：KST Def3.1。使われ方：底変更後の外積複体の chain 条件。 -/
theorem chartGeneratorEnumerationEquiv_differential (a : Fin (r + 1) → R)
    (i : Fin (r + 1)) (f : ChartRing R i →ₐ[R] B) :
    (chartKoszulDifferential (fun j => algebraMap R B (a j))
      (fun j => f (chartCoordinate R i j)) i).comp
        (chartGeneratorEnumerationEquiv (B := B) i).toLinearMap =
      Finsupp.linearCombination B (f ∘ chartKoszulSequence a i) := by
  apply Finsupp.lhom_ext
  intro j c
  simp [chartGeneratorEnumerationEquiv, finSuccAboveEquiv_apply, chartKoszulDifferential,
    chartKoszulSequence, chartRelation, chartCoordinate]

/-- 概要：チャート複体のスカラー拡大は像の関係式による外積複体と同型。
方針：Koszul の底変更・反復 cone 比較・生成元列挙を合成する。
規約：KST Def3.1、複体レベルの比較。
使われ方：重なり上でチャートの Koszul 基底変換を適用する。 -/
def chartBaseChangeExteriorIso (a : Fin (r + 1) → R) (i : Fin (r + 1))
    (f : ChartRing R i →ₐ[R] B) :
    baseChange f.toRingHom (derivedChartComplex a i) ≅
      chartExteriorCochain (fun j => algebraMap R B (a j))
        (fun j => f (chartCoordinate R i j)) i :=
  baseChangeKoszulIso f.toRingHom (chartKoszulSequence a i) ≪≫
    koszulExteriorIso (f ∘ chartKoszulSequence a i) ≪≫
      exteriorKoszulCochainIso (chartGeneratorEnumerationEquiv i)
        (Finsupp.linearCombination B (f ∘ chartKoszulSequence a i))
        (chartKoszulDifferential (fun j => algebraMap R B (a j))
          (fun j => f (chartCoordinate R i j)) i)
        (chartGeneratorEnumerationEquiv_differential a i f)

end SerrePositivity.KST.DerivedBlowup
