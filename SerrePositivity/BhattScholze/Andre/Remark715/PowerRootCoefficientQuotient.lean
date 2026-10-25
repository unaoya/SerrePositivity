module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomialModPrime

/-!
# André E1・E2：無限根環と任意の係数主イデアル商

## 概要

無限根多項式環の係数元 c による商は、係数環の c 商上の同じ無限根環と環同型。
BS Rem 7.15（著者版 p.62）の R/ϖ 上の具体的な無限根環への比較。

## 方針

係数商射の誘導する環射は全射。その核を各係数で調べて係数主イデアルと同定する。
第一同型定理で実商の同型を得る。

## 規約

p は正。c の正則性、係数環の標数や非零性を要求しない。

## 使われ方

prism の mod p 商内で c=x mod p として、ϖ 係数還元後の入力を比較する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p) (c : A)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "R" => A ⧸ Ideal.span {(c : A)}
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(c : A)})

/-- 概要：各係数を c 商へ送る無限根環の標準環射。
方針：加法モノイド環の係数射を使う。
規約：指数モノイドを保つ。
使われ方：BS Rem 7.15（著者版 p.62）の係数還元。 -/
def powerRootCoefficientQuotientMap : P →+* Pbar := AddMonoidAlgebra.mapRingHom G bar

/-- 概要：係数商射は単項式の係数だけを商へ送る。
方針：モノイド環の係数射の公式を使う。
規約：全ての係数・指数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数と変数の照合。 -/
theorem powerRootCoefficientQuotientMap_single (q : G) (b : A) :
    powerRootCoefficientQuotientMap A p hp c (AddMonoidAlgebra.single q b) =
      AddMonoidAlgebra.single q (bar b) := AddMonoidAlgebra.mapRingHom_single _ _ _

/-- 概要：係数商射は標準係数射と可換。
方針：零指数の単項式で計算する。
規約：元の係数環 A の元で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の入力多項式比較。 -/
theorem powerRootCoefficientQuotientMap_coeff (b : A) :
    powerRootCoefficientQuotientMap A p hp c (algebraMap A P b) =
      algebraMap R Pbar (bar b) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootCoefficientQuotientMap_single A p hp c 0 b

/-- 概要：無限根環の係数商射は全射。
方針：係数商射の全射性を有限台関数へ移す。
規約：係数環の非零性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の実商同型。 -/
theorem powerRootCoefficientQuotientMap_surjective :
    Function.Surjective (powerRootCoefficientQuotientMap A p hp c) :=
  AddMonoidAlgebra.map_surjective (bar).toAddMonoidHom Ideal.Quotient.mk_surjective

/-- 概要：係数商射の核は c の係数像の主イデアル。
方針：各係数の c 可除性から単項式を主イデアル内に足し戻す。
規約：c の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の台環の具体的な同定。 -/
theorem powerRootCoefficientQuotientMap_ker :
    RingHom.ker (powerRootCoefficientQuotientMap A p hp c) =
      Ideal.span {algebraMap A P c} := by
  classical
  apply le_antisymm
  · intro x hx
    have hzero : powerRootCoefficientQuotientMap A p hp c x = 0 := hx
    rw [← AddMonoidAlgebra.sum_coeff_single x]
    apply (Ideal.span {algebraMap A P c}).sum_mem
    intro q _
    have hcoeff : bar (x.coeff q) = 0 := by
      have h := congrArg (fun z : Pbar => z.coeff q) hzero
      simpa only [powerRootCoefficientQuotientMap, AddMonoidAlgebra.coeff_mapRingHom,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)
    rw [hb]
    have he : AddMonoidAlgebra.single q (c * b) =
        algebraMap A P c * AddMonoidAlgebra.single q b := by
      simp [AddMonoidAlgebra.coe_algebraMap]
    rw [he]
    exact (Ideal.span {algebraMap A P c}).mul_mem_right _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    intro t ht
    have ht' : t = algebraMap A P c := Set.mem_singleton_iff.mp ht
    subst t
    change powerRootCoefficientQuotientMap A p hp c (algebraMap A P c) = 0
    rw [powerRootCoefficientQuotientMap_coeff,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c), map_zero]

/-- 概要：無限根環の係数主イデアル商と係数商上の無限根環は環同型。
方針：核と全射性に第一同型定理を使う。
規約：実際の主イデアル商を用い、完備化はしない。
使われ方：BS Rem 7.15（著者版 p.62）の R/ϖ 無限根環への比較。 -/
def powerRootCoefficientQuotientEquiv :
    (P ⧸ Ideal.span {algebraMap A P c}) ≃+* Pbar :=
  (Ideal.quotEquivOfEq (powerRootCoefficientQuotientMap_ker A p hp c).symm).trans
    ((powerRootCoefficientQuotientMap A p hp c).quotientKerEquivOfSurjective
      (powerRootCoefficientQuotientMap_surjective A p hp c))

/-- 概要：係数商比較同型は代表元で係数商射に一致する。
方針：第一同型定理の標準公式を使う。
規約：無限根環の全ての元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の入力元の照合。 -/
theorem powerRootCoefficientQuotientEquiv_mk (t : P) :
    powerRootCoefficientQuotientEquiv A p hp c (Ideal.Quotient.mk _ t) =
      powerRootCoefficientQuotientMap A p hp c t := rfl

/-- 概要：係数商射は各 p 冪根変数を同じ番号の変数へ送る。
方針：係数 1 の単項式の公式を使う。
規約：全ての段を含める。
使われ方：BS Rem 7.15（著者版 p.62）の多項式入力の係数変更。 -/
theorem powerRootCoefficientQuotientMap_variable (n : ℕ) :
    powerRootCoefficientQuotientMap A p hp c (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable R p hp n := by
  simp only [powerRootPolynomialVariable, powerRootCoefficientQuotientMap_single, map_one]

/-- 概要：通常多項式の根変数での評価は係数商と可換。
方針：多項式評価の自然性と係数・変数の公式を使う。
規約：モニック性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の還元後のモニック入力の同定。 -/
theorem powerRootCoefficientQuotientMap_baseMap (f : Polynomial A) :
    powerRootCoefficientQuotientMap A p hp c (powerRootPolynomialBaseMap A p hp f) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    powerRootCoefficientQuotientMap_variable, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro b
  exact powerRootCoefficientQuotientMap_coeff A p hp c b

end SerrePositivity.BhattScholze.Andre
