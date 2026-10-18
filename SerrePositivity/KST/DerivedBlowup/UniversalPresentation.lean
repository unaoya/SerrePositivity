module

public import SerrePositivity.KST.DerivedBlowup.UniversalCharts
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Maps

/-!
概要：KST Def3.1・Lemma3.6 の普遍チャートの関係式による商表示。
方針：ℤ[T_j][S_j:j≠i] から ℤ[T_i,S_j:j≠i] への代入を構成する。
規約：このファイルは通常の環の商表示。Koszul 解消との比較は別工程。
使われ方：普遍 blowup チャートと導来底変更の Koszul 表示の接続。
-/

@[expose] public noncomputable section

universe v

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I]

/-- 概要：普遍チャートの T_i S_j−T_j の関係式族。
方針：一般のチャート関係式に普遍生成元 T_j を代入する。
規約：KST Def3.1。使われ方：商表示と普遍 Koszul 列。 -/
def universalRelation (i : I) (j : ChartIndex i) : ChartRing (UniversalBase I) i :=
  chartRelation (UniversalBase I) MvPolynomial.X i j.val

/-- 概要：普遍チャートの関係式が生成するイデアル。
方針：全 pivot 以外の関係式の span を取る。
規約：KST Def3.1。使われ方：通常の普遍チャートの商表示。 -/
def universalRelationIdeal (i : I) : Ideal (ChartRing (UniversalBase I) i) :=
  Ideal.span (Set.range (universalRelation i))

/-- 概要：普遍関係式を課した通常のチャート環。
方針：多項式環を関係式イデアルで割る。
規約：KST Def3.1、導来商との同定はここでは主張しない。
使われ方：ℤ[T_i,S_j] との明示的環同型の始域。 -/
abbrev UniversalPresentationQuotient (i : I) :=
  ChartRing (UniversalBase I) i ⧸ universalRelationIdeal i

/-- 概要：普遍チャートの多項式表示環から自由な radial 表示環への代入射。
方針：係数 T_j を T_i S_j、比座標 S_j をそのまま送る。
規約：KST Def3.1。使われ方：普遍商表示から自由多項式環への写像。 -/
def universalPresentationMap (i : I) :
    ChartRing (UniversalBase I) i →+* UniversalChart i :=
  MvPolynomial.eval₂Hom (universalBaseMap i).toRingHom (fun j => universalRatio i j.val)

/-- 概要：普遍代入射の係数上の値。
方針：eval₂ の係数公式。
規約：KST Def3.1。使われ方：普遍関係式の消滅。 -/
@[simp] theorem universalPresentationMap_C (i : I) (p : UniversalBase I) :
    universalPresentationMap i (MvPolynomial.C p) = universalBaseMap i p :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- 概要：普遍代入射の比変数上の値。
方針：eval₂ の生成元公式。
規約：KST Def3.1。使われ方：逆写像との生成元比較。 -/
@[simp] theorem universalPresentationMap_X (i : I) (j : ChartIndex i) :
    universalPresentationMap i (MvPolynomial.X j) = MvPolynomial.X (some j) := by
  simp [universalPresentationMap]

/-- 概要：普遍代入射は全ての関係式を消す。
方針：T_j=T_i S_j の係数公式を使う。
規約：KST Def3.1。使われ方：商環への因子化。 -/
@[simp] theorem universalPresentationMap_relation (i : I) (j : ChartIndex i) :
    universalPresentationMap i (universalRelation i j) = 0 := by
  simp [universalRelation, chartRelation, chartCoordinate, j.property]

/-- 概要：関係式商から自由な普遍チャート環への写像。
方針：関係式の消滅をイデアル span 全体へ延長する。
規約：KST Def3.1。使われ方：普遍商表示の環同型。 -/
def universalQuotientToChart (i : I) : UniversalPresentationQuotient i →+* UniversalChart i :=
  Ideal.Quotient.lift (universalRelationIdeal i) (universalPresentationMap i) (by
    have h : universalRelationIdeal i ≤ RingHom.ker (universalPresentationMap i) := by
      apply Ideal.span_le.mpr
      rintro p ⟨j, rfl⟩
      exact universalPresentationMap_relation i j
    exact fun p hp => h hp)

end SerrePositivity.KST.DerivedBlowup
