module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomialModPrime

/-!
# André A1-a：無限根多項式環の任意の係数主商

## 概要

無限根多項式環の任意の係数元による商は、係数環をその元で割った無限根環と同型。
モニック入力は各係数 p 冪商で正則となる。BS Rem 7.15（著者版 p.62）の完備入力。

## 方針

既存の mod p 比較の係数ごとの核計算を任意の係数元に一般化する。
原典を補う具体的な単項式の計算とモニック正則性による経路。

## 規約

根の指数を定める p と、係数商の元 a を区別する。p 正則性・素数性は不要。

## 使われ方

モニック商と p 完備化の交換に必要な、全 p 冪商での正則性を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p) (a : A)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "R" => A ⧸ Ideal.span {(a : A)}
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(a : A)})

/-- 概要：無限根多項式の係数を a 主商へ写す環射。
方針：同じ指数モノイド上の係数環射を使う。
規約：根の段や指数を変えない。
使われ方：BS Rem 7.15（著者版 p.62）の係数冪商比較。 -/
def powerRootPolynomialModScalarMap : P →+* Pbar :=
  AddMonoidAlgebra.mapRingHom G bar

/-- 概要：係数主商への無限根環の射は全射。
方針：係数商射の全射性を有限支持の係数写像へ移す。
規約：任意の係数元 a を許す。
使われ方：BS Rem 7.15（著者版 p.62）の実主商同型。 -/
theorem powerRootPolynomialModScalarMap_surjective :
    Function.Surjective (powerRootPolynomialModScalarMap A p hp a) :=
  AddMonoidAlgebra.map_surjective (bar).toAddMonoidHom Ideal.Quotient.mk_surjective

/-- 概要：係数主商への無限根環の射の核は係数 a の像の主イデアル。
方針：各係数を a の倍数に書き、有限和へ戻す。
規約：a の正則性や p との関係は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実係数商の同定。 -/
theorem powerRootPolynomialModScalarMap_ker :
    RingHom.ker (powerRootPolynomialModScalarMap A p hp a) =
      Ideal.span {algebraMap A P a} := by
  classical
  apply le_antisymm
  · intro x hx
    have hzero : powerRootPolynomialModScalarMap A p hp a x = 0 := hx
    rw [← AddMonoidAlgebra.sum_coeff_single x]
    apply (Ideal.span {algebraMap A P a}).sum_mem
    intro q _
    have hcoeff : bar (x.coeff q) = 0 := by
      have h := congrArg (fun z : Pbar => z.coeff q) hzero
      simpa only [powerRootPolynomialModScalarMap, AddMonoidAlgebra.coeff_mapRingHom,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)
    rw [hb]
    have he : AddMonoidAlgebra.single q (a * b) =
        algebraMap A P a * AddMonoidAlgebra.single q b := by
      change AddMonoidAlgebra.single q (a * b) =
        AddMonoidAlgebra.single 0 a * AddMonoidAlgebra.single q b
      rw [AddMonoidAlgebra.single_mul_single, zero_add]
    rw [he]
    exact (Ideal.span {algebraMap A P a}).mul_mem_right _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = _)
    change powerRootPolynomialModScalarMap A p hp a (algebraMap A P a) = 0
    simp [powerRootPolynomialModScalarMap, AddMonoidAlgebra.coe_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)]

/-- 概要：無限根環の係数 a 商は係数主商上の無限根環と環同型。
方針：核の同定と全射性から第一同型定理を使う。
規約：同じ実指数型を使う。
使われ方：BS Rem 7.15（著者版 p.62）のモニック正則性の移送。 -/
def powerRootPolynomialModScalarEquiv :
    (P ⧸ Ideal.span {algebraMap A P a}) ≃+* Pbar :=
  (Ideal.quotEquivOfEq (powerRootPolynomialModScalarMap_ker A p hp a).symm).trans
    ((powerRootPolynomialModScalarMap A p hp a).quotientKerEquivOfSurjective
      (powerRootPolynomialModScalarMap_surjective A p hp a))

/-- 概要：係数主商同型は代表元を係数ごとの商射で送る。
方針：第一同型定理の定義を展開する。
規約：全ての無限根多項式に適用する。
使われ方：BS Rem 7.15（著者版 p.62）の入力の追跡。 -/
theorem powerRootPolynomialModScalarEquiv_mk (x : P) :
    powerRootPolynomialModScalarEquiv A p hp a (Ideal.Quotient.mk _ x) =
      powerRootPolynomialModScalarMap A p hp a x := rfl

/-- 概要：モニック入力は任意の係数主商上で正則。
方針：係数主商同型に沿って、係数商上のモニック入力の正則性を戻す。
規約：a の正則性・非零性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の全 p 冪商での入力正則性。 -/
theorem powerRootPolynomial_monic_mod_scalar_regular (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular (P ⧸ Ideal.span {algebraMap A P a})
      (Ideal.Quotient.mk (Ideal.span {algebraMap A P a})
        (powerRootPolynomialBaseMap A p hp f)) := by
  let e := powerRootPolynomialModScalarEquiv A p hp a
  have he : e (Ideal.Quotient.mk _ (powerRootPolynomialBaseMap A p hp f)) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
    rw [powerRootPolynomialModScalarEquiv_mk]
    unfold powerRootPolynomialBaseMap
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
      Polynomial.eval₂_map]
    have hv : powerRootPolynomialModScalarMap A p hp a
        (powerRootPolynomialVariable A p hp 0) = powerRootPolynomialVariable R p hp 0 := by
      simp only [powerRootPolynomialVariable, powerRootPolynomialModScalarMap,
        AddMonoidAlgebra.mapRingHom_single, map_one]
    rw [hv]
    congr 1
    apply RingHom.ext
    intro b
    change powerRootPolynomialModScalarMap A p hp a (algebraMap A P b) =
      algebraMap R Pbar (bar b)
    simp [powerRootPolynomialModScalarMap, AddMonoidAlgebra.coe_algebraMap]
  have hr := powerRootPolynomial_monic_regular R p hp (f.map bar) (hf.map bar)
  intro x y hxy
  apply e.injective
  apply hr
  simpa only [smul_eq_mul, map_mul, he] using congrArg e hxy

/-- 概要：モニック入力は全ての p 冪商で正則。
方針：任意の係数主商の結果を pⁿ に適用する。
規約：係数環の p 正則性を追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の完備化とモニック商の交換。 -/
theorem powerRootPolynomial_monic_mod_prime_power_regular
    (f : Polynomial A) (hf : f.Monic) (n : ℕ) :
    IsSMulRegular (P ⧸ Ideal.span {(p : P) ^ n})
      (Ideal.Quotient.mk (Ideal.span {(p : P) ^ n}) (powerRootPolynomialBaseMap A p hp f)) := by
  have h := powerRootPolynomial_monic_mod_scalar_regular A p hp ((p : A) ^ n) f hf
  rw [map_pow, map_natCast] at h
  exact h

end SerrePositivity.BhattScholze.Andre
