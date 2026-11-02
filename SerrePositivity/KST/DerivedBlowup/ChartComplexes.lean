module

public import SerrePositivity.KST.DerivedBlowup.Charts
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic

/-!
概要：KST Def3.1・Lemma3.6 と §5.3 の有限チャートの Koszul 複体を構成する。
方針：L6 と共通の既存 koszulComplex を用い、関係式の列を明示する。
規約：cochain 規約、Koszul 生成元は次数−1。通常の商環に置き換えない。
使われ方：U_i、E∩U_i、D(n)∩U_i の underlying complex と外積模型との比較。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：i チャートの r 本の Koszul 関係式。
方針：Fin.succAbove により pivot を除いて列挙する。
規約：KST Def3.1、a_i S_j−a_j。使われ方：導来底変更の有限 Koszul 複体。 -/
def chartKoszulSequence (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    Fin r → ChartRing R i := fun j => chartRelation R a i (i.succAbove j)

/-- 概要：有限列挙は pivot 以外の関係式をちょうど尽くす。
方針：Fin.succAbove の像を用いる。規約：KST Def3.1、重複は関係式の値として許す。
使われ方：外積の ChartIndex 型との添字比較。 -/
theorem chartKoszulSequence_range (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    Set.range (chartKoszulSequence a i) =
      Set.range (fun j : ChartIndex i => chartRelation R a i j.val) := by
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨i.succAbove j, Fin.succAbove_ne i j⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq j.property
    exact ⟨k, by simp only [chartKoszulSequence, hk]⟩

/-- 概要：導来 blowup の i チャートの underlying Koszul 複体。
方針：既存の反復 cone 模型を指定された関係式に適用する。
規約：KST Def3.1、非正則列も許す。使われ方：チャート cdga との導来比較。 -/
def derivedChartComplex (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    CochainComplex (ModuleCat.{u} (ChartRing R i)) ℤ :=
  koszulComplex (chartKoszulSequence a i)

/-- 概要：例外因子の導来引き戻しの関係式列。
方針：チャートの列に Cartier 方程式 a_i を加える。
規約：KST Lemma3.6、例外因子は通常の a_i 商でなく導来商。
使われ方：Ko(A;a)[S] との可逆基底変換による比較。 -/
def exceptionalChartSequence (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    Fin (r + 1) → ChartRing R i :=
  Fin.snoc (chartKoszulSequence a i) (MvPolynomial.C (a i))

/-- 概要：例外因子の i チャートの underlying 複体。
方針：Cartier 方程式を含む全列の Koszul 複体を取る。
規約：KST Lemma3.6。使われ方：例外因子の構造層と基本 fiber 列。 -/
def exceptionalChartComplex (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    CochainComplex (ModuleCat.{u} (ChartRing R i)) ℤ :=
  koszulComplex (exceptionalChartSequence a i)

/-- 概要：例外因子の比較先 Ko(A;a)[S] の関係式列。
方針：全 a_j を多項式環の係数として送る。
規約：KST Lemma3.6。使われ方：exceptionalChartComplex との基底変換の目標。 -/
def exceptionalProductSequence (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    Fin (r + 1) → ChartRing R i := fun j => MvPolynomial.C (a j)

/-- 概要：D(n) のチャート関係式。
方針：チャート列に全ての a_j^n を加える。
規約：KST §5.3 p.33、n は自然数。使われ方：derived thickening の underlying 複体。 -/
def thickeningChartSequence (a : Fin (r + 1) → R) (i : Fin (r + 1)) (n : ℕ) :
    Fin (r + (r + 1)) → ChartRing R i :=
  Fin.addCases (chartKoszulSequence a i) (fun j => MvPolynomial.C (a j ^ n))

/-- 概要：D(n)∩U_i の underlying Koszul 複体。
方針：関係式の連結列を既存の反復 cone に渡す。
規約：KST §5.3、E(n) との同一視は別定理。使われ方：L7 が使う導来 thickening。 -/
def thickeningChartComplex (a : Fin (r + 1) → R) (i : Fin (r + 1)) (n : ℕ) :
    CochainComplex (ModuleCat.{u} (ChartRing R i)) ℤ :=
  koszulComplex (thickeningChartSequence a i n)

/-- 概要：導来チャートの構造複体は正の cochain 次数で零。
方針：既存 Koszul の次数境界。規約：KST Def3.1 の connective 性。
使われ方：dg 代数の整数次数構造と connective 条件。 -/
theorem derivedChartComplex_isZero_X_pos (a : Fin (r + 1) → R) (i : Fin (r + 1))
    (q : ℤ) (hq : 0 < q) : IsZero ((derivedChartComplex a i).X q) :=
  koszulComplex_isZero_X_of_pos (chartKoszulSequence a i) q hq

/-- 概要：導来チャートの構造複体は−r未満で零。
方針：r本の反復 cone の既存境界。規約：KST Lemma3.6 の有限表示。
使われ方：外積模型と反復 cone 模型を比較する有限次数範囲。 -/
theorem derivedChartComplex_isZero_X_lt (a : Fin (r + 1) → R) (i : Fin (r + 1))
    (q : ℤ) (hq : q < -(r : ℤ)) : IsZero ((derivedChartComplex a i).X q) :=
  koszulComplex_isZero_X_of_lt (chartKoszulSequence a i) q hq

end SerrePositivity.KST.DerivedBlowup
