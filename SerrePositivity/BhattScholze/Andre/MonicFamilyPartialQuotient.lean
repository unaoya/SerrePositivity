module

public import SerrePositivity.BhattScholze.Andre.MonicRelationResidue

/-!
# André E1・E2：独立な多項式関係の部分族による商

## 概要

先行変数だけの任意多項式関係で割った環は、その関係の商を係数とする残りの変数の
多項式環となる。残りの変数のモニック関係はこの商でも非零因子である。
BS 著者版 Cor 2.39（p.25）、Rem 7.15(1)（p.62）の有限独立関係族への準備。

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

@[expose] public noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}

/-- 概要：独立変数ごとの任意多項式関係が生成するイデアル。
方針：各多項式を対応変数で評価し、その像族の span を取る。
規約：名前によらずモニック性は定義には含めない。
使われ方：BS Rem 7.15（著者版 p.62）の関係族の通常商。 -/
def polynomialFamilyRelationIdeal {σ : Type v} (f : σ → Polynomial R) :
    Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun s => monicRelation (f s) s)

/-- 概要：直和の右側の変数の関係だけを課すイデアル。
方針：右側の添字を評価関係族に制限する。
規約：左側の変数には関係を課さない。
使われ方：BS Cor 2.39（著者版 p.25）の先行関係の商。 -/
def partialPolynomialRelationIdeal (f : τ ⊕ ι → Polynomial R) :
    Ideal (MvPolynomial (τ ⊕ ι) R) :=
  Ideal.span (Set.range fun s : ι => monicRelation (f (Sum.inr s)) (Sum.inr s))

/-- 概要：変数分割で右側の多項式関係は係数内の関係へ移る。
方針：多項式評価の自然性と変数分割同型の生成元公式を使う。
規約：任意多項式を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の部分族商の同定。 -/
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
使われ方：BS Cor 2.39（著者版 p.25）の有限族計算の通常商。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の独立関係の正則性を再利用する。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の実係数作用を追跡する。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の係数射の比較。 -/
theorem partialPolynomialQuotientEquiv_C (f : τ ⊕ ι → Polynomial R) (a : R) :
    partialPolynomialQuotientEquiv f (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      MvPolynomial.C (Ideal.Quotient.mk
        (polynomialFamilyRelationIdeal (fun s : ι => f (Sum.inr s))) (MvPolynomial.C a)) := by
  rw [partialPolynomialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_C, MvPolynomial.map_C]

/-- 概要：商同型は残りの変数をそのまま多項式変数へ送る。
方針：代表元公式と変数分割の公式を使う。
規約：先行変数には適用しない。
使われ方：BS Cor 2.39（著者版 p.25）の後続関係の同定。 -/
theorem partialPolynomialQuotientEquiv_X_inl (f : τ ⊕ ι → Polynomial R) (s : τ) :
    partialPolynomialQuotientEquiv f (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl s))) =
      MvPolynomial.X s := by
  rw [partialPolynomialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.map_X]

/-- 概要：先行関係商の下で残りのモニック関係は非零因子。
方針：多項式環表示へ移し、係数変更したモニック関係の正則性を適用する。
規約：先行多項式には制限せず、対象となる関係だけモニックとする。
使われ方：BS Cor 2.39（著者版 p.25）の独立関係族の正則性入力。 -/
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
