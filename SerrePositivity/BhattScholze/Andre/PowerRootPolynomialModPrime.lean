module

public import SerrePositivity.BhattScholze.Andre.PowerRootMonicQuotient
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# André E1・E2：無限 p 冪根多項式環の実 mod p 係数比較

## 概要

無限 p 冪根多項式環を p で割ることと、係数環を p で割って同じ指数モノイド環を
作ることは可換である。BS Rem 7.15（著者版 p.62）の無限根変数上の正則性の入力。

## 方針

係数商射から誘導される環射の全射性と、核が p 主イデアルであることを係数ごとに証明する。
第一同型定理を用いて実商同士の同型を構成する。

## 規約

p は正の自然数。素数性、係数環の標数・非零性・p 正則性は不要。
同じ実指数モノイドと標準係数射を保持する。

## 使われ方

mod p のモニック多項式を係数商上でモニックとして扱い、無限根環での正則性を得る。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "R" => A ⧸ Ideal.span {(p : A)}
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 概要：無限根多項式の各係数を mod p に送る標準環射。
方針：加法モノイド環の係数環射を使う。
規約：指数と全根変数の番号は変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の係数商比較。 -/
def powerRootPolynomialModPrimeMap : P →+* Pbar :=
  AddMonoidAlgebra.mapRingHom G bar

/-- 概要：係数商射は各単項式の係数だけを mod p に送る。
方針：モノイド環の係数写像の単項式公式を使う。
規約：任意の係数・指数について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の変数と係数の照合。 -/
theorem powerRootPolynomialModPrimeMap_single (q : G) (a : A) :
    powerRootPolynomialModPrimeMap A p hp (AddMonoidAlgebra.single q a) =
      AddMonoidAlgebra.single q (bar a) :=
  AddMonoidAlgebra.mapRingHom_single _ _ _

/-- 概要：係数商射は標準係数射と可換。
方針：係数を零指数の単項式として計算する。
規約：同じ元の係数環 A からの作用を比較する。
使われ方：BS Rem 7.15（著者版 p.62）の通常多項式評価の自然性。 -/
theorem powerRootPolynomialModPrimeMap_coeff (a : A) :
    powerRootPolynomialModPrimeMap A p hp (algebraMap A P a) = algebraMap R Pbar (bar a) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using powerRootPolynomialModPrimeMap_single A p hp 0 a

/-- 概要：無限根多項式の係数商射は全射。
方針：元の係数商射の全射性をモノイド環へ移す。
規約：有限支持を保って係数を持ち上げる既存の構成を使う。
使われ方：BS Rem 7.15（著者版 p.62）の実商比較同型の存在。 -/
theorem powerRootPolynomialModPrimeMap_surjective :
    Function.Surjective (powerRootPolynomialModPrimeMap A p hp) :=
  AddMonoidAlgebra.map_surjective (bar).toAddMonoidHom Ideal.Quotient.mk_surjective

/-- 概要：無限根多項式の係数商射の核は同じ環内の p 主イデアル。
方針：核の元の全係数が p で割れることを使い、各単項式を p の倍数として足し戻す。
規約：係数環の非零性や p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実 mod p 商の同定。 -/
theorem powerRootPolynomialModPrimeMap_ker :
    RingHom.ker (powerRootPolynomialModPrimeMap A p hp) = Ideal.span {(p : P)} := by
  classical
  apply le_antisymm
  · intro x hx
    have hzero : powerRootPolynomialModPrimeMap A p hp x = 0 := hx
    rw [← AddMonoidAlgebra.sum_coeff_single x]
    apply (Ideal.span {(p : P)}).sum_mem
    intro q _
    have hcoeff : bar (x.coeff q) = 0 := by
      have h := congrArg (fun z : Pbar => z.coeff q) hzero
      simpa only [powerRootPolynomialModPrimeMap, AddMonoidAlgebra.coeff_mapRingHom,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)
    rw [hb]
    have he : AddMonoidAlgebra.single q ((p : A) * b) =
        (p : P) * AddMonoidAlgebra.single q b := by
      rw [AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single, zero_add]
    rw [he]
    exact (Ideal.span {(p : P)}).mul_mem_right _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = _)
    change powerRootPolynomialModPrimeMap A p hp (p : P) = 0
    rw [map_natCast]
    have hpR : (p : R) = 0 := by
      change bar (p : A) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R Pbar) hpR

/-- 概要：実無限根環の mod p 商は係数商上の同じ無限根環と環同型。
方針：係数商射の核の同定と全射性に第一同型定理を適用する。
規約：同じ指数型を用い、完備化は行わない。
使われ方：BS Rem 7.15（著者版 p.62）のモニック入力の mod p 正則性の移送。 -/
def powerRootPolynomialModPrimeEquiv :
    (P ⧸ Ideal.span {(p : P)}) ≃+* Pbar :=
  (Ideal.quotEquivOfEq (powerRootPolynomialModPrimeMap_ker A p hp).symm).trans
    ((powerRootPolynomialModPrimeMap A p hp).quotientKerEquivOfSurjective
      (powerRootPolynomialModPrimeMap_surjective A p hp))

/-- 概要：実 mod p 比較同型は商代表元を係数商射で送る。
方針：第一同型定理による同型の代表元公式を使う。
規約：全ての元について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の多項式評価の比較。 -/
theorem powerRootPolynomialModPrimeEquiv_mk (x : P) :
    powerRootPolynomialModPrimeEquiv A p hp (Ideal.Quotient.mk _ x) =
      powerRootPolynomialModPrimeMap A p hp x := rfl

/-- 概要：係数商射は全根変数を同じ番号の根変数へ送る。
方針：係数 1 の単項式の公式を使う。
規約：任意の段 n を含める。
使われ方：BS Rem 7.15（著者版 p.62）のモニック評価の自然性。 -/
theorem powerRootPolynomialModPrimeMap_variable (n : ℕ) :
    powerRootPolynomialModPrimeMap A p hp (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable R p hp n := by
  simp only [powerRootPolynomialVariable, powerRootPolynomialModPrimeMap_single, map_one]

/-- 概要：通常多項式の無限根変数での評価は係数を mod p にする操作と可換。
方針：評価の環射に関する自然性と係数・変数の比較公式を使う。
規約：この恒等式にモニック性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実残余関係式の同定。 -/
theorem powerRootPolynomialModPrimeMap_baseMap (f : Polynomial A) :
    powerRootPolynomialModPrimeMap A p hp (powerRootPolynomialBaseMap A p hp f) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    powerRootPolynomialModPrimeMap_variable, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro a
  exact powerRootPolynomialModPrimeMap_coeff A p hp a


/-- 概要：無限根環のモニック入力は実 mod p 商でも非零因子。
方針：実係数商比較で、係数商上のモニック多項式の既存の正則性へ移す。
規約：元の係数環の p 正則性・非零性・素数性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根環上の実分冪包への正則入力。 -/
theorem powerRootPolynomial_monic_mod_prime_regular (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular (P ⧸ Ideal.span {(p : P)})
      (Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootPolynomialBaseMap A p hp f)) := by
  let e := powerRootPolynomialModPrimeEquiv A p hp
  have he : e (Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootPolynomialBaseMap A p hp f)) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
    rw [powerRootPolynomialModPrimeEquiv_mk, powerRootPolynomialModPrimeMap_baseMap]
  have hr := powerRootPolynomial_monic_regular R p hp (f.map bar) (hf.map bar)
  intro x z hxz
  apply e.injective
  apply hr
  have h := congrArg e hxz
  simpa only [smul_eq_mul, map_mul, he] using h

end SerrePositivity.BhattScholze.Andre
