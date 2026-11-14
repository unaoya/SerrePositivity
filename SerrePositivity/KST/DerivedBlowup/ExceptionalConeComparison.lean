module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.DerivedBlowup.KoszulConeComparison
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
概要：KST Lemma3.6 の例外因子チャートの二つの Koszul 表示の比較。
方針：末尾の Cartier 方程式を pivot の位置へ移し、証明済みの可逆基底変換を適用する。
規約：反復 cone 模型と外積模型の比較を明示的に介する。
使われ方：E∩U_i の underlying 複体を Ko(A;a)[S] と同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：末尾を pivot へ移し、残りを succAbove の順に並べる置換。
方針：pivot を除く Option 表示を経由する。
規約：KST Lemma3.6。使われ方：例外因子の関係式の列挙の比較。 -/
def exceptionalSequencePermutation (i : Fin (r + 1)) : Fin (r + 1) ≃ Fin (r + 1) :=
  (finSuccEquiv' (Fin.last r)).trans (finSuccEquiv' i).symm

/-- 概要：例外因子の関係式列の自由生成元と全添字の生成元の同型。
方針：末尾と pivot の列挙置換を自由加群へ持ち上げる。
規約：KST Lemma3.6。使われ方：外積基底変換への入力。 -/
def exceptionalSequenceGeneratorEquiv (i : Fin (r + 1)) :
    (Fin (r + 1) →₀ ChartRing R i) ≃ₗ[ChartRing R i] (Fin (r + 1) →₀ ChartRing R i) :=
  Finsupp.domLCongr (exceptionalSequencePermutation i)

/-- 概要：例外因子の関係式列の列挙同型は Koszul 微分を保つ。
方針：castSucc と last の生成元で関係式を比較する。
規約：KST Lemma3.6。使われ方：反復 cone と例外外積模型の比較。 -/
theorem exceptionalSequenceGeneratorEquiv_differential (a : Fin (r + 1) → R)
    (i : Fin (r + 1)) :
    (Finsupp.linearCombination (ChartRing R i)
      (exceptionalRelationValue (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i)).comp
        (exceptionalSequenceGeneratorEquiv (R := R) i).toLinearMap =
      Finsupp.linearCombination (ChartRing R i) (exceptionalChartSequence a i) := by
  apply Finsupp.lhom_ext
  intro j c
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [exceptionalSequenceGeneratorEquiv, exceptionalSequencePermutation,
      exceptionalChartSequence, exceptionalRelationValue]
  · simp [exceptionalSequenceGeneratorEquiv, exceptionalSequencePermutation,
      finSuccEquiv'_last_apply_castSucc, exceptionalChartSequence, exceptionalRelationValue,
      Fin.succAbove_ne, chartKoszulSequence, chartRelation]

/-- 概要：例外因子の反復 cone 複体と全添字の外積複体の同型。
方針：有限列の Koszul 比較と列挙同型を合成する。
規約：KST Lemma3.6。使われ方：例外因子の基底変換の実際の複体への適用。 -/
def exceptionalChartExteriorIso (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    exceptionalChartComplex a i ≅
      exceptionalExteriorCochain (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i :=
  koszulExteriorIso (exceptionalChartSequence a i) ≪≫
    exteriorKoszulCochainIso (exceptionalSequenceGeneratorEquiv i)
      (Finsupp.linearCombination (ChartRing R i) (exceptionalChartSequence a i))
      (Finsupp.linearCombination (ChartRing R i)
        (exceptionalRelationValue (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i))
      (exceptionalSequenceGeneratorEquiv_differential a i)

/-- 概要：例外因子チャートの複体を全 a_j の Koszul 複体と同定する。
方針：外積模型上の可逆生成元変換を両側の反復 cone 比較で挟む。
規約：KST Lemma3.6、正則性不要。使われ方：E∩U_i ≃ Ko(A;a)[S] の複体部分。 -/
def exceptionalChartProductIso (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    exceptionalChartComplex a i ≅ koszulComplex (exceptionalProductSequence a i) :=
  exceptionalChartExteriorIso a i ≪≫
    exceptionalExteriorCochainIso (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i ≪≫
      (koszulExteriorIso (exceptionalProductSequence a i)).symm

/-- 概要：例外因子チャートの複体は Ko(A;a) の多項式環への底変更。
方針：全 a_j の Koszul 表示と既存 baseChangeKoszulIso を合成する。
規約：KST Lemma3.6、ここでは underlying 複体の底変更。
使われ方：例外因子の係数つき表示と射影空間への比較。 -/
def exceptionalChartBaseChangeIso (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    exceptionalChartComplex a i ≅
      baseChange (MvPolynomial.C : R →+* ChartRing R i) (koszulComplex a) :=
  exceptionalChartProductIso a i ≪≫ (baseChangeKoszulIso MvPolynomial.C a).symm

end SerrePositivity.KST.DerivedBlowup

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (1.8)" (partial := component) "仮定：普遍多項式模型の指定チャートと有限列（Lean が強い）。結論：導来底変換の二種類の局所比較。通常・導来両側を含む全立方体は未接続（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalChartBaseChangeIso
attribute [cite KST "Lemma 3.5" (partial := component) "仮定：指定普遍チャートとその底変換（Lean が強い）。結論：例外因子の dg チャートの比較と古典チャートの表示。正則列を保つ射全般の通常ブローアップと全厚化の導来 Cartesian 性は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalChartBaseChangeIso
attribute [cite KST "Lemma 5.5" (partial := component) "仮定：有限生成ホモロジーを持つ複体の Koszul 塔、または指定例外因子のチャート（Lean が強い）。結論：プロホモロジー比較と局所の例外因子の底変換。K の絶対・相対スペクトルに移す三つの同値は未接続（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalChartBaseChangeIso
