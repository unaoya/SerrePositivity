module

public import SerrePositivity.BhattScholze.Andre.PowerRootCoefficientQuotient

/-!
# André E1・E2：無限根環と任意の係数イデアル商

## 概要

無限根多項式環を係数イデアル I で割ると A/I 上の同じ無限根環と環同型。
BS Rem 7.15（著者版 p.62）の二元商上の入力環を具体化する。

## 方針

係数変更射の全射性と核を有限台関数の各係数で計算する。

## 規約

I の主性・正則性・係数環の非零性を仮定しない。

## 使われ方

(p,d) 商上の主 pd 表示を R/ϖ 上の無限根入力へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p) (I : Ideal A)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "R" => A ⧸ I
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "bar" => Ideal.Quotient.mk I
local notation "J" => I.map (algebraMap A P)

/-- 概要：各係数を I 商へ送る無限根環の標準環射。
方針：加法モノイド環の係数射を使う。
規約：指数モノイドを保つ。
使われ方：BS Rem 7.15（著者版 p.62）の係数還元。 -/
def powerRootCoefficientIdealQuotientMap : P →+* Pbar := AddMonoidAlgebra.mapRingHom G bar

/-- 概要：係数商射は単項式の係数だけを商へ送る。
方針：モノイド環の係数射の公式を使う。
規約：全ての係数・指数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数と変数の照合。 -/
theorem powerRootCoefficientIdealQuotientMap_single (q : G) (b : A) :
    powerRootCoefficientIdealQuotientMap A p hp I (AddMonoidAlgebra.single q b) =
      AddMonoidAlgebra.single q (bar b) := AddMonoidAlgebra.mapRingHom_single _ _ _

/-- 概要：係数商射は標準係数射と可換。
方針：零指数の単項式で計算する。
規約：元の係数環 A の元で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の入力多項式比較。 -/
theorem powerRootCoefficientIdealQuotientMap_coeff (b : A) :
    powerRootCoefficientIdealQuotientMap A p hp I (algebraMap A P b) =
      algebraMap R Pbar (bar b) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootCoefficientIdealQuotientMap_single A p hp I 0 b

/-- 概要：無限根環の係数商射は全射。
方針：係数商射の全射性を有限台関数へ移す。
規約：係数環の非零性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の実商同型。 -/
theorem powerRootCoefficientIdealQuotientMap_surjective :
    Function.Surjective (powerRootCoefficientIdealQuotientMap A p hp I) :=
  AddMonoidAlgebra.map_surjective (bar).toAddMonoidHom Ideal.Quotient.mk_surjective

/-- 概要：係数商射の核は 係数イデアル I の像イデアル。
方針：各係数の I への所属から単項式を像イデアル内に足し戻す。
規約：I の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の台環の具体的な同定。 -/
theorem powerRootCoefficientIdealQuotientMap_ker :
    RingHom.ker (powerRootCoefficientIdealQuotientMap A p hp I) =
      J := by
  classical
  apply le_antisymm
  · intro x hx
    have hzero : powerRootCoefficientIdealQuotientMap A p hp I x = 0 := hx
    rw [← AddMonoidAlgebra.sum_coeff_single x]
    apply (J).sum_mem
    intro q _
    have hcoeff : bar (x.coeff q) = 0 := by
      have h := congrArg (fun z : Pbar => z.coeff q) hzero
      simpa only [powerRootCoefficientIdealQuotientMap, AddMonoidAlgebra.coeff_mapRingHom,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h
    have hcoeffI : x.coeff q ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hcoeff
    have he : AddMonoidAlgebra.single q (x.coeff q) =
        algebraMap A P (x.coeff q) * AddMonoidAlgebra.single q 1 := by
      simp [AddMonoidAlgebra.coe_algebraMap]
    rw [he]
    exact (J).mul_mem_right _ (Ideal.mem_map_of_mem _ hcoeffI)
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change powerRootCoefficientIdealQuotientMap A p hp I (algebraMap A P b) = 0
    rw [powerRootCoefficientIdealQuotientMap_coeff,
      Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]

/-- 概要：無限根環の係数イデアル商と係数商上の無限根環は環同型。
方針：核と全射性に第一同型定理を使う。
規約：実際のイデアル商を用い、完備化はしない。
使われ方：BS Rem 7.15（著者版 p.62）の R/ϖ 無限根環への比較。 -/
def powerRootCoefficientIdealQuotientEquiv :
    (P ⧸ J) ≃+* Pbar :=
  (Ideal.quotEquivOfEq (powerRootCoefficientIdealQuotientMap_ker A p hp I).symm).trans
    ((powerRootCoefficientIdealQuotientMap A p hp I).quotientKerEquivOfSurjective
      (powerRootCoefficientIdealQuotientMap_surjective A p hp I))

/-- 概要：係数商比較同型は代表元で係数商射に一致する。
方針：第一同型定理の標準公式を使う。
規約：無限根環の全ての元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の入力元の照合。 -/
theorem powerRootCoefficientIdealQuotientEquiv_mk (t : P) :
    powerRootCoefficientIdealQuotientEquiv A p hp I (Ideal.Quotient.mk _ t) =
      powerRootCoefficientIdealQuotientMap A p hp I t := rfl

/-- 概要：係数商射は各 p 冪根変数を同じ番号の変数へ送る。
方針：係数 1 の単項式の公式を使う。
規約：全ての段を含める。
使われ方：BS Rem 7.15（著者版 p.62）の多項式入力の係数変更。 -/
theorem powerRootCoefficientIdealQuotientMap_variable (n : ℕ) :
    powerRootCoefficientIdealQuotientMap A p hp I (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable R p hp n := by
  simp only [powerRootPolynomialVariable, powerRootCoefficientIdealQuotientMap_single, map_one]

/-- 概要：通常多項式の根変数での評価は係数商と可換。
方針：多項式評価の自然性と係数・変数の公式を使う。
規約：モニック性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の還元後のモニック入力の同定。 -/
theorem powerRootCoefficientIdealQuotientMap_baseMap (f : Polynomial A) :
    powerRootCoefficientIdealQuotientMap A p hp I (powerRootPolynomialBaseMap A p hp f) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    powerRootCoefficientIdealQuotientMap_variable, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro b
  exact powerRootCoefficientIdealQuotientMap_coeff A p hp I b

end SerrePositivity.BhattScholze.Andre
