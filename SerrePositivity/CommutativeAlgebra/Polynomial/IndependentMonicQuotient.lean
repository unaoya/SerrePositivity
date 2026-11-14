module
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Order.Notation
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Defs
public import SerrePositivity.CommutativeAlgebra.Polynomial.MonicRelation

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Fintype.Option

/-!
# 独立なモニック関係による多項式商

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v w

/-! ## André E1・E2：独立な多項式関係の部分族による商（旧 Andre/MonicFamilyPartialQuotient.lean）

## 概要

先行変数だけの任意多項式関係で割った環は、その関係の商を係数とする残りの変数の
多項式環となる。残りの変数のモニック関係はこの商でも非零因子である。
BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15(1)（p.62）の有限独立関係族への準備。

## 方針

変数の直和分割と、係数商と多変数多項式環の交換同型を使う。
既存 B4-6 の冪根関係に固有な表示を使わず、先行多項式を任意に取る。

## 規約

先行関係にはモニック性・正次数・有限性を要求しない。
正則性を主張する残りの関係についてだけモニック性を要求する。
この商表示だけでは元の係数環上の忠実平坦性を結論しない。

## 使われ方

モニック族とその冪の先行商での正則性、および raw δ 除算の有限族入力に用いる。
-/

@[expose] public noncomputable section MonicFamilyPartialQuotient

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}

/-- 概要：独立変数ごとの任意多項式関係が生成するイデアル。
方針：各多項式を対応変数で評価し、その像族の span を取る。
規約：名前によらずモニック性は定義には含めない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の関係族の通常商。 -/
def polynomialFamilyRelationIdeal {σ : Type v} (f : σ → Polynomial R) :
    Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun s => monicRelation (f s) s)

/-- 概要：直和の右側の変数の関係だけを課すイデアル。
方針：右側の添字を評価関係族に制限する。
規約：左側の変数には関係を課さない。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の先行関係の商。 -/
def partialPolynomialRelationIdeal (f : τ ⊕ ι → Polynomial R) :
    Ideal (MvPolynomial (τ ⊕ ι) R) :=
  Ideal.span (Set.range fun s : ι => monicRelation (f (Sum.inr s)) (Sum.inr s))

/-- 概要：変数分割で右側の多項式関係は係数内の関係へ移る。
方針：多項式評価の自然性と変数分割同型の生成元公式を使う。
規約：任意多項式を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の部分族商の同定。 -/
theorem monicRelation_sum_inr (f : Polynomial R) (s : ι) :
    MvPolynomial.sumRingEquiv R τ ι (monicRelation f (Sum.inr s)) =
      MvPolynomial.C (monicRelation f s) := by
  let e := MvPolynomial.sumRingEquiv R τ ι
  change e.toRingHom (f.eval₂ MvPolynomial.C (MvPolynomial.X (Sum.inr s))) = _
  rw [Polynomial.hom_eval₂]
  have hc : e.toRingHom.comp MvPolynomial.C =
      (MvPolynomial.C : MvPolynomial ι R →+* MvPolynomial τ (MvPolynomial ι R)).comp
        MvPolynomial.C := by
    apply RingHom.ext
    intro a
    exact MvPolynomial.sumRingEquiv_C R τ ι a
  rw [hc]
  have hx : e.toRingHom (MvPolynomial.X (Sum.inr s)) =
      MvPolynomial.C (MvPolynomial.X s) := MvPolynomial.sumRingEquiv_X_inr R τ ι s
  rw [hx]
  change f.eval₂ _ (MvPolynomial.C (MvPolynomial.X s)) = _
  exact (Polynomial.hom_eval₂ f MvPolynomial.C MvPolynomial.C (MvPolynomial.X s)).symm

/-- 概要：変数分割は先行関係のイデアルを係数イデアルの拡張へ送る。
方針：各生成元の像を計算して span の像を同定する。
規約：族の有限性を要求しない。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の有限族計算の通常商。 -/
theorem partialPolynomialRelationIdeal_map_sum (f : τ ⊕ ι → Polynomial R) :
    (partialPolynomialRelationIdeal f).map (MvPolynomial.sumRingEquiv R τ ι).toRingHom =
      (polynomialFamilyRelationIdeal (fun s : ι => f (Sum.inr s))).map
        (MvPolynomial.C : MvPolynomial ι R →+* MvPolynomial τ (MvPolynomial ι R)) := by
  simp only [partialPolynomialRelationIdeal, polynomialFamilyRelationIdeal, Ideal.map_span,
    ← Set.range_comp']
  congr 1
  congr 1
  funext s
  exact monicRelation_sum_inr _ s

/-- 概要：先行関係の商は先行関係商を係数とする残りの多項式環。
方針：変数分割の商同型と係数商の交換同型を合成する。
規約：先行関係のモニック性や有限性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の独立関係の正則性を再利用する。 -/
def partialPolynomialQuotientEquiv (f : τ ⊕ ι → Polynomial R) :
    (MvPolynomial (τ ⊕ ι) R ⧸ partialPolynomialRelationIdeal f) ≃+*
      MvPolynomial τ (MvPolynomial ι R ⧸
        polynomialFamilyRelationIdeal (fun s : ι => f (Sum.inr s))) :=
  (Ideal.quotientEquiv _ _ (MvPolynomial.sumRingEquiv R τ ι)
    (partialPolynomialRelationIdeal_map_sum f).symm).trans
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ)
        (polynomialFamilyRelationIdeal (fun s : ι => f (Sum.inr s)))).symm.toRingEquiv

/-- 概要：部分族商の同型は実係数商による多項式写像で与えられる。
方針：商同型の代表元公式と既存の係数商の可換式を使う。
規約：元の係数射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実係数作用を追跡する。 -/
theorem partialPolynomialQuotientEquiv_mk (f : τ ⊕ ι → Polynomial R)
    (x : MvPolynomial (τ ⊕ ι) R) :
    partialPolynomialQuotientEquiv f (Ideal.Quotient.mk _ x) =
      MvPolynomial.map (Ideal.Quotient.mk
        (polynomialFamilyRelationIdeal (fun s : ι => f (Sum.inr s))))
          (MvPolynomial.sumRingEquiv R τ ι x) := by
  change (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) _).symm
    (Ideal.Quotient.mk _ (MvPolynomial.sumRingEquiv R τ ι x)) = _
  exact DFunLike.congr_fun (monicPowerFamilyCoefficientQuotient_comp τ
    (MvPolynomial ι R) (polynomialFamilyRelationIdeal (fun s : ι => f (Sum.inr s)))) _

/-- 概要：商同型は元の係数を先行商の係数像へ送る。
方針：代表元公式に定数多項式を代入する。
規約：通常の係数作用を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数射の比較。 -/
theorem partialPolynomialQuotientEquiv_C (f : τ ⊕ ι → Polynomial R) (a : R) :
    partialPolynomialQuotientEquiv f (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      MvPolynomial.C (Ideal.Quotient.mk
        (polynomialFamilyRelationIdeal (fun s : ι => f (Sum.inr s))) (MvPolynomial.C a)) := by
  rw [partialPolynomialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_C, MvPolynomial.map_C]

/-- 概要：商同型は残りの変数をそのまま多項式変数へ送る。
方針：代表元公式と変数分割の公式を使う。
規約：先行変数には適用しない。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の後続関係の同定。 -/
theorem partialPolynomialQuotientEquiv_X_inl (f : τ ⊕ ι → Polynomial R) (s : τ) :
    partialPolynomialQuotientEquiv f (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl s))) =
      MvPolynomial.X s := by
  rw [partialPolynomialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.map_X]

/-- 概要：先行関係商の下で残りのモニック関係は非零因子。
方針：多項式環表示へ移し、係数変更したモニック関係の正則性を適用する。
規約：先行多項式には制限せず、対象となる関係だけモニックとする。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の独立関係族の正則性入力。 -/
theorem partialPolynomialQuotient_remaining_isSMulRegular
    (f : τ ⊕ ι → Polynomial R) (h : Polynomial R) (hh : h.Monic) (s : τ) :
    IsSMulRegular (MvPolynomial (τ ⊕ ι) R ⧸ partialPolynomialRelationIdeal f)
      (Ideal.Quotient.mk (partialPolynomialRelationIdeal f)
        (monicRelation h (Sum.inl s))) := by
  let Q := MvPolynomial ι R ⧸ polynomialFamilyRelationIdeal (fun s : ι => f (Sum.inr s))
  let c : R →+* Q := (Ideal.Quotient.mk _).comp MvPolynomial.C
  let e := partialPolynomialQuotientEquiv f
  have he : e (Ideal.Quotient.mk _ (monicRelation h (Sum.inl s))) =
      monicRelation (h.map c) s := by
    let g := e.toRingHom.comp (Ideal.Quotient.mk _)
    change g (h.eval₂ MvPolynomial.C (MvPolynomial.X (Sum.inl s))) = _
    rw [Polynomial.hom_eval₂]
    have hc : g.comp MvPolynomial.C = MvPolynomial.C.comp c := by
      apply RingHom.ext
      intro a
      exact partialPolynomialQuotientEquiv_C f a
    rw [hc]
    change h.eval₂ _ (e (Ideal.Quotient.mk _
      (MvPolynomial.X (Sum.inl s)))) = _
    rw [partialPolynomialQuotientEquiv_X_inl]
    rw [monicRelation, Polynomial.eval₂_map]
  have h := monicRelation_isSMulRegular (h.map c) (hh.map c) s
  intro x y hxy
  apply e.injective
  apply h
  have heq := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using heq

end SerrePositivity.BhattScholze.Andre

end MonicFamilyPartialQuotient

/-! ## André E1・E2：任意の先行多項式族の商でのモニック正則性（旧 Andre/MonicFamilySubsetRegular.lean）

## 概要

先行する任意の変数集合に各一変数多項式の関係を課しても、集合外の変数における
モニック多項式は非零因子である。BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15(1)（p.62）の準備。

## 方針

添字集合を先行集合と補集合に分割し、前工程の多項式環としての部分族商表示を適用する。

## 規約

先行族には有限性もモニック性も不要。正則性を主張する多項式だけモニックとする。
元の係数環上の忠実平坦性は別工程である。

## 使われ方

先行モニック関係の冪商を扱い、δ p 除算の有限族の正則性入力を供給する。
-/

@[expose] public noncomputable section MonicFamilySubsetRegular

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：多項式関係の評価は変数の再添字付けと可換。
方針：環射による評価の自然性を適用する。
規約：再添字写像の単射性もモニック性も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の先行変数分離。 -/
theorem monicRelation_rename {R : Type u} [CommRing R] {σ : Type v} {τ : Type w}
    (ρ : σ → τ) (f : Polynomial R) (s : σ) :
    MvPolynomial.rename ρ (monicRelation f s) = monicRelation f (ρ s) := by
  unfold monicRelation
  change (MvPolynomial.rename ρ).toRingHom
    (f.eval₂ MvPolynomial.C (MvPolynomial.X s)) = _
  rw [Polynomial.hom_eval₂]
  have hx : (MvPolynomial.rename ρ).toRingHom (MvPolynomial.X s : MvPolynomial σ R) =
      MvPolynomial.X (ρ s) :=
    MvPolynomial.rename_X ρ s
  rw [hx]
  have hc : (MvPolynomial.rename ρ).toRingHom.comp (MvPolynomial.C : R →+* MvPolynomial σ R) =
      MvPolynomial.C := by
    apply RingHom.ext
    intro a
    exact MvPolynomial.rename_C _ _
  rw [hc]

variable {R : Type u} [CommRing R] {σ : Type v}

/-- 概要：先行集合の関係だけを生成元に持つイデアル。
方針：添字を指定集合の部分型に制限して span を取る。
規約：先行多項式は任意。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の有限先行関係の商。 -/
def polynomialSubsetRelationIdeal (T : Set σ) (f : σ → Polynomial R) :
    Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun s : T => monicRelation (f s) (s : σ))

/-- 概要：元の添字を残りの添字と先行添字に分ける同値。
方針：集合と補集合の直和同値を反転して並べ替える。
規約：古典論理による所属判定を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の独立変数分離。 -/
def polynomialSubsetIndexEquiv (T : Set σ) : σ ≃ (Tᶜ : Set σ) ⊕ T := by
  classical
  exact (Equiv.Set.sumCompl T).symm.trans (Equiv.sumComm _ _)

/-- 概要：先行変数は添字分割の右側に対応する。
方針：集合の直和同値を簡約する。
規約：集合の部分型で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の先行イデアルの同定。 -/
theorem polynomialSubsetIndexEquiv_mem (T : Set σ) (s : T) :
    polynomialSubsetIndexEquiv T s = Sum.inr s := by
  classical
  simp [polynomialSubsetIndexEquiv]

/-- 概要：残りの変数は添字分割の左側に対応する。
方針：集合の直和同値を簡約する。
規約：補集合の部分型で述べる。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の後続関係の同定。 -/
theorem polynomialSubsetIndexEquiv_notMem (T : Set σ) (s : (Tᶜ : Set σ)) :
    polynomialSubsetIndexEquiv T s = Sum.inl s := by
  classical
  simp [polynomialSubsetIndexEquiv]

/-- 概要：添字分割は先行関係イデアルを直和右側の関係イデアルへ送る。
方針：各評価関係の再添字公式と生成元の集合像を用いる。
規約：先行集合の有限性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実商の比較。 -/
theorem polynomialSubsetRelationIdeal_map_rename (T : Set σ) (f : σ → Polynomial R) :
    (polynomialSubsetRelationIdeal T f).map
      (MvPolynomial.renameEquiv R (polynomialSubsetIndexEquiv T)).toRingHom =
    partialPolynomialRelationIdeal
      (Sum.elim (fun s : (Tᶜ : Set σ) => f s) (fun s : T => f s)) := by
  simp only [polynomialSubsetRelationIdeal, partialPolynomialRelationIdeal,
    Ideal.map_span, ← Set.range_comp']
  congr 1
  congr 1
  funext s
  change MvPolynomial.rename _ (monicRelation (f s) (s : σ)) = _
  rw [monicRelation_rename, polynomialSubsetIndexEquiv_mem]
  rfl

/-- 概要：先行族に含まれない変数の任意モニック関係は先行商でも非零因子。
方針：添字分割の商に移し、直和版の後続関係の正則性を適用する。
規約：先行多項式 f と後続多項式 h を独立に取る。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）のモニック族の p 乗先行商の正則性。 -/
theorem polynomialSubsetQuotient_remaining_isSMulRegular
    (T : Set σ) (f : σ → Polynomial R) (h : Polynomial R) (hh : h.Monic)
    (s : σ) (hs : s ∉ T) :
    IsSMulRegular (MvPolynomial σ R ⧸ polynomialSubsetRelationIdeal T f)
      (Ideal.Quotient.mk (polynomialSubsetRelationIdeal T f) (monicRelation h s)) := by
  let F := Sum.elim (fun s : (Tᶜ : Set σ) => f s) (fun s : T => f s)
  let e := Ideal.quotientEquiv _ _
    (MvPolynomial.renameEquiv R (polynomialSubsetIndexEquiv T)).toRingEquiv
    (polynomialSubsetRelationIdeal_map_rename T f).symm
  have he : e (Ideal.Quotient.mk _ (monicRelation h s)) =
      Ideal.Quotient.mk (partialPolynomialRelationIdeal F)
        (monicRelation h (Sum.inl (⟨s, hs⟩ : (Tᶜ : Set σ)))) := by
    rw [Ideal.quotientEquiv_mk]
    change Ideal.Quotient.mk _ (MvPolynomial.rename _ (monicRelation h s)) = _
    rw [monicRelation_rename, polynomialSubsetIndexEquiv_notMem T ⟨s, hs⟩]
  have hr := partialPolynomialQuotient_remaining_isSMulRegular F h hh
    (⟨s, hs⟩ : (Tᶜ : Set σ))
  intro x y hxy
  apply e.injective
  apply hr
  have heq := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using heq

end SerrePositivity.BhattScholze.Andre

end MonicFamilySubsetRegular

/-! ## André E1・E2：通常の多項式根族商の普遍性（旧 Andre/MonicFamilyQuotientUniversal.lean）

## 概要

独立変数ごとの多項式関係の商における根方程式と、指定根を持つ任意の環への普遍射を構成する。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の通常モニック根添加の準備である。

## 方針

多変数多項式環の評価射を関係イデアルで降下させる。
係数と根上の公式を明示し、変数一つ追加の商と AdjoinRoot の比較に使う。

## 規約

この普遍性にはモニック性や正次数を要求しない。
商の自由性・忠実平坦性は別の結果であり、この普遍性だけからは結論しない。

## 使われ方

有限モニック族の通常商を一元根添加の反復と同定し、任意族の遷移射を固定する。
-/

