module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyPartialQuotient
public import Mathlib.Logic.Equiv.Set

/-!
# André E1・E2：任意の先行多項式族の商でのモニック正則性

## 概要

先行する任意の変数集合に各一変数多項式の関係を課しても、集合外の変数における
モニック多項式は非零因子である。BS 著者版 Cor 2.39（p.25）、Rem 7.15(1)（p.62）の準備。

## 方針

添字集合を先行集合と補集合に分割し、前工程の多項式環としての部分族商表示を適用する。

## 規約

先行族には有限性もモニック性も不要。正則性を主張する多項式だけモニックとする。
元の係数環上の忠実平坦性は別工程である。

## 使われ方

先行モニック関係の冪商を扱い、δ p 除算の有限族の正則性入力を供給する。
-/

@[expose] public noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：多項式関係の評価は変数の再添字付けと可換。
方針：環射による評価の自然性を適用する。
規約：再添字写像の単射性もモニック性も不要。
使われ方：BS Rem 7.15（著者版 p.62）の先行変数分離。 -/
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
使われ方：BS Cor 2.39（著者版 p.25）の有限先行関係の商。 -/
def polynomialSubsetRelationIdeal (T : Set σ) (f : σ → Polynomial R) :
    Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun s : T => monicRelation (f s) (s : σ))

/-- 概要：元の添字を残りの添字と先行添字に分ける同値。
方針：集合と補集合の直和同値を反転して並べ替える。
規約：古典論理による所属判定を使う。
使われ方：BS Rem 7.15（著者版 p.62）の独立変数分離。 -/
def polynomialSubsetIndexEquiv (T : Set σ) : σ ≃ (Tᶜ : Set σ) ⊕ T := by
  classical
  exact (Equiv.Set.sumCompl T).symm.trans (Equiv.sumComm _ _)

/-- 概要：先行変数は添字分割の右側に対応する。
方針：集合の直和同値を簡約する。
規約：集合の部分型で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の先行イデアルの同定。 -/
theorem polynomialSubsetIndexEquiv_mem (T : Set σ) (s : T) :
    polynomialSubsetIndexEquiv T s = Sum.inr s := by
  classical
  simp [polynomialSubsetIndexEquiv]

/-- 概要：残りの変数は添字分割の左側に対応する。
方針：集合の直和同値を簡約する。
規約：補集合の部分型で述べる。
使われ方：BS Cor 2.39（著者版 p.25）の後続関係の同定。 -/
theorem polynomialSubsetIndexEquiv_notMem (T : Set σ) (s : (Tᶜ : Set σ)) :
    polynomialSubsetIndexEquiv T s = Sum.inl s := by
  classical
  simp [polynomialSubsetIndexEquiv]

/-- 概要：添字分割は先行関係イデアルを直和右側の関係イデアルへ送る。
方針：各評価関係の再添字公式と生成元の集合像を用いる。
規約：先行集合の有限性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の実商の比較。 -/
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

/-- 概要：先行関係で割った環は先行関係商上の補集合の多項式環。
方針：添字分割の商同型と直和版の商表示を合成する。
規約：先行関係の正則性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の独立変数族の通常代数。 -/
def polynomialSubsetQuotientEquiv (T : Set σ) (f : σ → Polynomial R) :
    (MvPolynomial σ R ⧸ polynomialSubsetRelationIdeal T f) ≃+*
      MvPolynomial (Tᶜ : Set σ)
        (MvPolynomial T R ⧸ polynomialFamilyRelationIdeal (fun s : T => f s)) :=
  (Ideal.quotientEquiv _ _
    (MvPolynomial.renameEquiv R (polynomialSubsetIndexEquiv T)).toRingEquiv
    (polynomialSubsetRelationIdeal_map_rename T f).symm).trans
      (partialPolynomialQuotientEquiv
        (Sum.elim (fun s : (Tᶜ : Set σ) => f s) (fun s : T => f s)))

/-- 概要：先行族に含まれない変数の任意モニック関係は先行商でも非零因子。
方針：添字分割の商に移し、直和版の後続関係の正則性を適用する。
規約：先行多項式 f と後続多項式 h を独立に取る。
使われ方：BS Cor 2.39（著者版 p.25）のモニック族の p 乗先行商の正則性。 -/
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
