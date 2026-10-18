module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.Ring

/-!
# 導来 blowup の標準チャートの座標

概要：KST Def 3.1・Lemma 3.6（pp.11–14）の Koszul チャートに使う座標環を構成する。
方針：一つの同次座標を1に規格化し、重なりでは可逆座標で割る。
規約：このファイルの多項式環は導来チャートの次数零の表示環。通常の商環を導来商と同一視しない。
使われ方：Koszul の関係式の変換と O(1) の推移単元の cocycle を計算する。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I]

/-- 概要：pivot 以外の座標の添字。方針：部分型で変数を除く。
規約：KST Def 3.1 の i チャート。使われ方：余分な S_i という変数を持たない表示環。 -/
abbrev ChartIndex (i : I) := {j : I // j ≠ i}

/-- 概要：標準チャートの多項式環。方針：pivot 以外を自由変数にする。
規約：KST Lemma 3.6 の底変更前の表示。使われ方：Koszul 関係式の係数環。 -/
abbrev ChartRing (R : Type u) [CommRing R] (i : I) := MvPolynomial (ChartIndex i) R

variable (R : Type u) [CommRing R]

/-- 概要：pivot を含む規格化座標。方針：S_i=1、それ以外は多項式の変数。
規約：KST §3.1、S_j=Y_j/Y_i。使われ方：全添字で一様に座標変換を書く。 -/
def chartCoordinate (i j : I) : ChartRing R i :=
  if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

@[simp] theorem chartCoordinate_self (i : I) : chartCoordinate R i i = 1 := by
  simp [chartCoordinate]

@[simp] theorem chartCoordinate_other (i : I) (j : ChartIndex i) :
    chartCoordinate R i j.val = MvPolynomial.X j := by
  simp [chartCoordinate, j.property]

/-- 概要：導来底変更の Koszul 関係式。方針：a_i S_j−a_j を表示環に置く。
規約：KST Def 3.1、非正則列も許す。使われ方：導来チャートの Koszul 複体の入力列。 -/
def chartRelation (a : I → R) (i j : I) : ChartRing R i :=
  MvPolynomial.C (a i) * chartCoordinate R i j - MvPolynomial.C (a j)

@[simp] theorem chartRelation_self (a : I → R) (i : I) : chartRelation R a i i = 0 := by
  simp [chartRelation]

variable {R} {B : Type w} [CommRing B]

/-- 概要：単元で割る同次座標の規格化。方針：逆元を units のデータから取る。
規約：KST §3.1 の重なりの公式。使われ方：零因子を含む任意の基底環での座標変換。 -/
def normalizeCoordinates (x : I → B) (s : Bˣ) (j : I) : B := x j * ↑s⁻¹

omit [DecidableEq I] in
/-- 概要：可逆な pivot 座標の規格化値は1。方針：単元の逆元律。
規約：KST Def 3.1 のチャート遷移。使われ方：変換先チャートの pivot 条件。 -/
theorem normalizeCoordinates_pivot (x : I → B) (k : I) (s : Bˣ) (hs : ↑s = x k) :
    normalizeCoordinates x s k = 1 := by
  rw [normalizeCoordinates, ← hs]
  exact s.mul_inv

omit [DecidableEq I] in
/-- 概要：二回の規格化の cocycle。方針：二つの単元の積でまとめる。
規約：KST §3.1 の三重重なり、可換環。使われ方：Koszul 基底変換の係数の cocycle。 -/
theorem normalizeCoordinates_cocycle (x : I → B) (s t : Bˣ) :
    normalizeCoordinates (normalizeCoordinates x s) t = normalizeCoordinates x (s * t) := by
  funext j
  simp [normalizeCoordinates, mul_assoc, mul_comm]

omit [DecidableEq I] in
/-- 概要：O(1) の推移単元の cocycle。方針：規格化後の単元を元の単元へ掛け戻す。
規約：KST §3.1、s=S_k^(i)、t=S_l^(k)。使われ方：O(1) の貼り合わせの係数。 -/
theorem transitionUnit_cocycle (x : I → B) (l : I) (s t : Bˣ)
    (ht : ↑t = normalizeCoordinates x s l) : ↑(s * t) = x l := by
  rw [Units.val_mul, ht, normalizeCoordinates]
  calc
    ↑s * (x l * ↑s⁻¹) = x l * (↑s * ↑s⁻¹) := mul_left_comm _ _ _
    _ = x l := by simp

variable [Algebra R B]

omit [DecidableEq I] in
/-- 概要：チャート環の代数射は基底係数を保つ。方針：代数射の係数保存。
規約：KST Def3.1 の基底上のチャート。使われ方：Koszul 関係式の変換計算。 -/
@[simp] theorem chartAlgHom_C (i : I) (f : ChartRing R i →ₐ[R] B) (r : R) :
    f (MvPolynomial.C r) = algebraMap R B r := f.commutes r

/-- 概要：可逆座標上のチャート間の環射。方針：規格化した変数を aeval に渡す。
規約：KST §3.1、スキームの向きと逆に k チャートから i チャートの重なりへ。
使われ方：局所化環に値を取る具体的なチャート遷移。 -/
def chartTransition (i k : I) (f : ChartRing R i →ₐ[R] B) (s : Bˣ) :
    ChartRing R k →ₐ[R] B :=
  MvPolynomial.aeval (fun j : ChartIndex k =>
    normalizeCoordinates (fun l => f (chartCoordinate R i l)) s j.val)

/-- 概要：チャート環射は全ての規格化座標を商の公式へ送る。
方針：pivot とそれ以外を分け aeval の生成元計算を使う。
規約：KST Def 3.1、s は i チャートでの k 座標。使われ方：遷移環射の cocycle 検証。 -/
theorem chartTransition_coordinate (i k j : I) (f : ChartRing R i →ₐ[R] B) (s : Bˣ)
    (hs : ↑s = f (chartCoordinate R i k)) :
    chartTransition i k f s (chartCoordinate R k j) =
      normalizeCoordinates (fun l => f (chartCoordinate R i l)) s j := by
  by_cases h : j = k
  · subst j
    simp only [chartCoordinate_self, map_one]
    exact (normalizeCoordinates_pivot _ k s hs).symm
  · simp [chartCoordinate, h, chartTransition]

/-- 概要：二つのチャート環射は三重重なりで一つの環射に一致する。
方針：多項式の生成元で座標規格化の cocycle を使う。
規約：KST §3.1、全ての単元は同じ重なり環 B に取る。使われ方：環図式の厳密な cocycle。 -/
theorem chartTransition_cocycle (i k l : I) (f : ChartRing R i →ₐ[R] B) (s t : Bˣ)
    (hs : ↑s = f (chartCoordinate R i k))
    (ht : ↑t = chartTransition i k f s (chartCoordinate R k l)) :
    chartTransition k l (chartTransition i k f s) t = chartTransition i l f (s * t) := by
  have hst : ↑(s * t) = f (chartCoordinate R i l) := by
    apply transitionUnit_cocycle (fun j => f (chartCoordinate R i j)) l s t
    rw [ht, chartTransition_coordinate i k l f s hs]
  ext j
  rw [← chartCoordinate_other R l j,
    chartTransition_coordinate k l j.val (chartTransition i k f s) t ht,
    chartTransition_coordinate i l j.val f (s * t) hst]
  simp only [chartTransition_coordinate i k _ f s hs]
  exact congrFun (normalizeCoordinates_cocycle (fun q => f (chartCoordinate R i q)) s t) j.val

/-- 概要：i チャートの O(1) の推移単元を掛け戻すと l 座標になる。
方針：環射による座標公式と単元 cocycle を合わせる。
規約：KST §3.1、Thomason Lemme2.3 の可逆層の準備。
使われ方：同じ重なり環での O(1) の三重 cocycle。 -/
theorem chartTransition_unit_cocycle (i k l : I) (f : ChartRing R i →ₐ[R] B) (s t : Bˣ)
    (hs : ↑s = f (chartCoordinate R i k))
    (ht : ↑t = chartTransition i k f s (chartCoordinate R k l)) :
    ↑(s * t) = f (chartCoordinate R i l) := by
  apply transitionUnit_cocycle (fun j => f (chartCoordinate R i j)) l s t
  rw [ht, chartTransition_coordinate i k l f s hs]

/-- 概要：Koszul 関係式のチャート遷移の係数を計算する。
方針：R_kj=R_ij−(S_j/S_k)R_ik を単元の逆元律で証明する。
規約：KST Def3.1 の非正則列を許す表示。使われ方：Koszul 生成元の基底変換の行列。 -/
theorem chartTransition_relation (a : I → R) (i k j : I)
    (f : ChartRing R i →ₐ[R] B) (s : Bˣ)
    (hs : ↑s = f (chartCoordinate R i k)) :
    chartTransition i k f s (chartRelation R a k j) =
      f (chartRelation R a i j) -
        normalizeCoordinates (fun q => f (chartCoordinate R i q)) s j *
          f (chartRelation R a i k) := by
  simp only [chartRelation, map_sub, map_mul, chartAlgHom_C,
    chartTransition_coordinate i k j f s hs, normalizeCoordinates]
  rw [← hs]
  have h := s.mul_inv
  calc
    algebraMap R B (a k) * (f (chartCoordinate R i j) * ↑s⁻¹) - algebraMap R B (a j) =
        (algebraMap R B (a i) * f (chartCoordinate R i j) - algebraMap R B (a j)) -
          (f (chartCoordinate R i j) * ↑s⁻¹) *
            (algebraMap R B (a i) * ↑s - algebraMap R B (a k)) := by
      calc
        _ = algebraMap R B (a i) * f (chartCoordinate R i j) - algebraMap R B (a j) -
            (algebraMap R B (a i) * f (chartCoordinate R i j) * (↑s * ↑s⁻¹) -
              algebraMap R B (a k) * (f (chartCoordinate R i j) * ↑s⁻¹)) := by rw [h]; ring
        _ = _ := by ring

end SerrePositivity.KST.DerivedBlowup
