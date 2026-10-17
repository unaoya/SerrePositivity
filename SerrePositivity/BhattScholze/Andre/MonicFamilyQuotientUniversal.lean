module

public import SerrePositivity.BhattScholze.Andre.MonicFamilySubsetRegular
public import SerrePositivity.BhattScholze.Andre.OrdinaryMonicRoot

/-!
# André E1・E2：通常の多項式根族商の普遍性

## 概要

独立変数ごとの多項式関係の商における根方程式と、指定根を持つ任意の環への普遍射を構成する。
BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）の通常モニック根添加の準備である。

## 方針

多変数多項式環の評価射を関係イデアルで降下させる。
係数と根上の公式を明示し、変数一つ追加の商と AdjoinRoot の比較に使う。

## 規約

この普遍性にはモニック性や正次数を要求しない。
商の自由性・忠実平坦性は別の結果であり、この普遍性だけからは結論しない。

## 使われ方

有限モニック族の通常商を一元根添加の反復と同定し、任意族の遷移射を固定する。
-/

@[expose] public noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {σ : Type v}

/-- 概要：独立な多項式関係をすべて課した通常の根族商。
方針：既存の関係イデアルで多変数多項式環を割る。
規約：零商も許す。モニック性は定義に含めない。
使われ方：BS Thm 7.14（著者版 p.61）の通常根添加環。 -/
abbrev PolynomialFamilyQuotient (f : σ → Polynomial R) :=
  MvPolynomial σ R ⧸ polynomialFamilyRelationIdeal f

/-- 概要：各関係の指定根は変数の標準商像である。
方針：対応する変数を関係商へ写す。
規約：係数作用は通常の R 代数作用に固定する。
使われ方：BS Rem 7.15（著者版 p.62）の根方程式を明示する。 -/
def polynomialFamilyQuotientRoot (f : σ → Polynomial R) (s : σ) :
    PolynomialFamilyQuotient f :=
  Ideal.Quotient.mk _ (MvPolynomial.X s)

/-- 概要：通常の根族商の標準根は元の多項式の根となる。
方針：評価の自然性と関係イデアルの生成元の消滅を使う。
規約：元の係数環の代数作用に関して述べる。
使われ方：BS Thm 7.14（著者版 p.61）の通常根族の構成。 -/
theorem polynomialFamilyQuotient_eval (f : σ → Polynomial R) (s : σ) :
    (f s).eval₂ (algebraMap R (PolynomialFamilyQuotient f))
      (polynomialFamilyQuotientRoot f s) = 0 := by
  let q := Ideal.Quotient.mk (polynomialFamilyRelationIdeal f)
  change (f s).eval₂ (q.comp MvPolynomial.C) (q (MvPolynomial.X s)) = 0
  rw [← Polynomial.hom_eval₂]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self s))

/-- 概要：指定された根を持つ任意の環へ根族商からの実環射を構成する。
方針：多変数評価射が関係生成元を消すことから商に降下する。
規約：任意の係数環射と根族を指定する。
使われ方：BS Rem 7.15（著者版 p.62）の一変数追加と商の比較。 -/
def polynomialFamilyQuotientLift {S : Type w} [CommRing S]
    (f : σ → Polynomial R) (φ : R →+* S) (a : σ → S)
    (ha : ∀ s, (f s).eval₂ φ (a s) = 0) : PolynomialFamilyQuotient f →+* S := by
  apply Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom φ a)
  change polynomialFamilyRelationIdeal f ≤ RingHom.ker (MvPolynomial.eval₂Hom φ a)
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  change (MvPolynomial.eval₂Hom φ a) (monicRelation (f s) s) = 0
  unfold monicRelation
  rw [Polynomial.hom_eval₂]
  simpa using ha s

/-- 概要：普遍射は標準根を指定根へ送る。
方針：商射の代表元公式と多変数評価の変数公式を使う。
規約：指定された根方程式の証明は任意。
使われ方：BS Thm 7.14（著者版 p.61）の根を保持する遷移。 -/
theorem polynomialFamilyQuotientLift_root {S : Type w} [CommRing S]
    (f : σ → Polynomial R) (φ : R →+* S) (a : σ → S)
    (ha : ∀ s, (f s).eval₂ φ (a s) = 0) (s : σ) :
    polynomialFamilyQuotientLift f φ a ha (polynomialFamilyQuotientRoot f s) = a s := by
  exact MvPolynomial.eval₂Hom_X' φ a s

/-- 概要：普遍射は元の係数射を延長する。
方針：商射の代表元公式と多変数評価の係数公式を使う。
規約：通常の R 代数構造に対する公式。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数作用を保つ。 -/
theorem polynomialFamilyQuotientLift_coeff {S : Type w} [CommRing S]
    (f : σ → Polynomial R) (φ : R →+* S) (a : σ → S)
    (ha : ∀ s, (f s).eval₂ φ (a s) = 0) (x : R) :
    polynomialFamilyQuotientLift f φ a ha (algebraMap R (PolynomialFamilyQuotient f) x) =
      φ x := by
  exact MvPolynomial.eval₂Hom_C φ a x

/-- 概要：根族商からの環射は係数と標準根上の値で一意に決まる。
方針：商射と多変数多項式環の生成元に関する外延性を使う。
規約：標的に通常の環構造だけを要求する。
使われ方：BS Rem 7.15（著者版 p.62）の商表示の相互逆性。 -/
theorem polynomialFamilyQuotientHom_ext {S : Type w} [CommRing S]
    (f : σ → Polynomial R) (F G : PolynomialFamilyQuotient f →+* S)
    (hc : ∀ x : R, F (algebraMap R _ x) = G (algebraMap R _ x))
    (hx : ∀ s, F (polynomialFamilyQuotientRoot f s) =
      G (polynomialFamilyQuotientRoot f s)) : F = G := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · exact hc
  · exact hx

end SerrePositivity.BhattScholze.Andre
