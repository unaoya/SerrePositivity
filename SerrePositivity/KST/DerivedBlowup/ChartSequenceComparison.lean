module

public import SerrePositivity.KST.DerivedBlowup.ExteriorSequence
public import SerrePositivity.KST.DerivedBlowup.ChartCochainMaps
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
概要：KST Def3.1 の標準チャートの二つの生成元の添字を比較する。
方針：Fin.succAbove による自由加群の同型を外積複体の同型へ持ち上げる。
規約：列の外積模型と ChartIndex 外積模型の比較。反復 cone とはまだ比較しない。
使われ方：既存反復 cone 模型との比較に使う添字の橋渡し。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：チャート列と pivot を除いた生成元加群の標準同型。
方針：finSuccAboveEquiv による自由加群の添字変更。
規約：KST Def3.1。使われ方：有限列と ChartIndex の外積模型の比較。 -/
def chartSequenceGeneratorEquiv (i : Fin (r + 1)) :
    (Fin r →₀ ChartRing R i) ≃ₗ[ChartRing R i] (ChartIndex i →₀ ChartRing R i) :=
  Finsupp.domLCongr (finSuccAboveEquiv i)

/-- 概要：チャートの生成元列挙の同型は Koszul 微分を保つ。
方針：標準基底で関係式 a_i S_j−a_j を比較する。
規約：KST Def3.1。使われ方：外積複体同型の chain 条件。 -/
theorem chartSequenceGeneratorEquiv_differential (a : Fin (r + 1) → R)
    (i : Fin (r + 1)) :
    (chartKoszulDifferential (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i).comp
      (chartSequenceGeneratorEquiv (R := R) i).toLinearMap =
      Finsupp.linearCombination (ChartRing R i) (chartKoszulSequence a i) := by
  apply Finsupp.lhom_ext
  intro j c
  simp [chartSequenceGeneratorEquiv, finSuccAboveEquiv_apply,
    chartKoszulDifferential, chartKoszulSequence, chartRelation, chartCoordinate]

/-- 概要：チャート関係式列の外積模型と ChartIndex 模型は同型。
方針：生成元列挙の同型と微分比較を外積 cochain 同型へ持ち上げる。
規約：KST Def3.1、反復 cone 模型との比較は別工程。
使われ方：チャート外積模型を有限列の Koszul として扱う。 -/
def chartSequenceExteriorIso (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    sequenceExteriorCochain (chartKoszulSequence a i) ≅
      chartExteriorCochain (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i :=
  exteriorKoszulCochainIso (chartSequenceGeneratorEquiv i)
    (Finsupp.linearCombination (ChartRing R i) (chartKoszulSequence a i))
    (chartKoszulDifferential (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i)
    (chartSequenceGeneratorEquiv_differential a i)

end SerrePositivity.KST.DerivedBlowup
