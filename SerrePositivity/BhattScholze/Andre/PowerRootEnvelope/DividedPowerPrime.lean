module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.RankOneDP
public import SerrePositivity.BhattScholze.Delta.DividedPower.Principal.PrincipalDP
public import SerrePositivity.BhattScholze.Delta.DividedPower.Coefficients.Factorial
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Flat.Basic
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# 標数 p の一元分冪代数の切断表示（BS 著者版 Remark 7.15 の事実 (1)）

## 概要
素数次数シフト、素数冪の分冪生成元と切断変数からの全射、テンソル分解・有限切断段の評価と普遍性・単射性、可算切断表示 A[g₁,g₂,…]/(gᵢᵖ)、正次数商・正則元・p 局所環での分冪構造の降下、階乗部分環の mod p 分冪、一元分冪表示環の自由性と移送。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/PowerRootInput`、`PowerRootEnvelope/PrincipalDP`、`PowerRootEnvelope/Varpi`、`Variants/MonicRootedExtension`。
-/

universe u v w

/-! ## 係数環同型に沿う一元分冪表示の移送

## 概要

係数環同型 A≃B は自由一元分冪代数と γ₁=y の一次関係商の環同型を誘導する。
標準係数・全標準生成元を保つ。BS 著者版 Remark 7.15(1)（著者版 p.62）の係数比較への準備。

## 方針

既存の分冪代数の係数変更射を実環射として束ね、単項式基底で逆合成を確認する。
一次関係の生成イデアルを照合して実商同型へ降ろす。

## 規約

係数環の標数・正則性・非零性を要求しない。分冪構造の存在はこの通常環同型と別に扱う。

## 使われ方

無限根環の実 mod p 商と、係数商上の無限根環の間で実 pd 包の台環を移す。
-/

@[expose] public noncomputable section PrincipalDPRingEquiv

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 概要：自由一元分冪代数の環射は係数と γₙ(1) の値で決まる。
方針：一方の係数射から終域に A 作用を与え、標準分冪基底上の線形外延性を使う。
規約：終域に事前の A 代数構造を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数同型による逆合成の検証。 -/
theorem rankOneDPRingHom_ext {T : Type w} [CommRing T]
    (f g : DividedPowerAlgebra A A →+* T)
    (hc : ∀ a, f (algebraMap A _ a) = g (algebraMap A _ a))
    (hγ : ∀ n, f (DividedPowerAlgebra.dp A n (1 : A)) =
      g (DividedPowerAlgebra.dp A n (1 : A))) : f = g := by
  let : Algebra A T := (f.comp (algebraMap A (DividedPowerAlgebra A A))).toAlgebra
  let ff : DividedPowerAlgebra A A →ₐ[A] T := { f with commutes' := fun _ => rfl }
  let gg : DividedPowerAlgebra A A →ₐ[A] T := { g with commutes' := fun a => (hc a).symm }
  have he : ff = gg := by
    apply AlgHom.toLinearMap_injective
    apply (rankOneDPAnyBasis A).ext
    intro n
    simpa only [AlgHom.toLinearMap_apply, rankOneDPAnyBasis_apply, ff, gg, AlgHom.coe_mk] using hγ n
  exact congrArg AlgHom.toRingHom he

/-- 概要：任意の係数環射は自由一元分冪代数の実環射を誘導する。
方針：係数環射の指定する代数構造を局所導入して既存の分冪代数写像を使う。
規約：元の台環と係数作用は変更しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更の具体的な環射。 -/
def rankOneDPRingMap (φ : A →+* B) : DividedPowerAlgebra A A →+* DividedPowerAlgebra B B := by
  letI := φ.toAlgebra
  exact (DividedPowerAlgebra.map B (Algebra.linearMap A B)).toRingHom

/-- 概要：誘導された環射は標準係数を元の係数環射で送る。
方針：分冪代数の係数代数射の可換性を使う。
規約：終域の自然な B 係数射で値を述べる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の表示関係の係数の照合。 -/
theorem rankOneDPRingMap_coeff (φ : A →+* B) (a : A) :
    rankOneDPRingMap φ (algebraMap A _ a) = algebraMap B _ (φ a) := by
  let := φ.toAlgebra
  exact (DividedPowerAlgebra.map B (Algebra.linearMap A B)).commutes a

/-- 概要：誘導環射は標準分冪 γₙ(1) を同じ次数の標準分冪へ送る。
方針：分冪代数写像の生成元公式と係数射の単位保存を使う。
規約：全ての次数 n を含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の表示関係と標準生成元の照合。 -/
theorem rankOneDPRingMap_dp (φ : A →+* B) (n : ℕ) :
    rankOneDPRingMap φ (DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp B n (1 : B) := by
  let := φ.toAlgebra
  change DividedPowerAlgebra.map B (Algebra.linearMap A B)
    (DividedPowerAlgebra.dp A n (1 : A)) = _
  rw [DividedPowerAlgebra.map_apply_dp, Algebra.linearMap_apply, map_one]

/-- 概要：係数環同型は自由一元分冪代数の環同型を誘導する。
方針：正逆の係数変更射の合成を係数と標準基底上で確認する。
規約：標数や非零性の仮定は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の一次関係商の同型の構成。 -/
def rankOneDPRingEquiv (e : A ≃+* B) : DividedPowerAlgebra A A ≃+* DividedPowerAlgebra B B :=
  RingEquiv.ofRingHom (rankOneDPRingMap e.toRingHom) (rankOneDPRingMap e.symm.toRingHom)
    (by
      apply rankOneDPRingHom_ext
      · intro b
        simp only [RingHom.comp_apply, rankOneDPRingMap_coeff, RingHom.id_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      · intro n
        simp only [RingHom.comp_apply, rankOneDPRingMap_dp, RingHom.id_apply])
    (by
      apply rankOneDPRingHom_ext
      · intro a
        simp only [RingHom.comp_apply, rankOneDPRingMap_coeff, RingHom.id_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
      · intro n
        simp only [RingHom.comp_apply, rankOneDPRingMap_dp, RingHom.id_apply])

/-- 概要：自由分冪の係数同型は標準係数を対応させる。
方針：同型の順射の係数公式を使う。
規約：実係数射の値として述べる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の一次関係イデアルの比較。 -/
theorem rankOneDPRingEquiv_coeff (e : A ≃+* B) (a : A) :
    rankOneDPRingEquiv e (algebraMap A _ a) = algebraMap B _ (e a) :=
  rankOneDPRingMap_coeff e.toRingHom a

/-- 概要：自由分冪の係数同型は標準分冪の次数を保つ。
方針：同型の順射の生成元公式を使う。
規約：全ての n を含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の標準生成元の比較。 -/
theorem rankOneDPRingEquiv_dp (e : A ≃+* B) (n : ℕ) :
    rankOneDPRingEquiv e (DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp B n (1 : B) :=
  rankOneDPRingMap_dp e.toRingHom n

/-- 概要：一次関係イデアルは係数同型で対応する一次関係イデアルへ移る。
方針：生成元 γ₁(1)-y の像を係数と分冪の公式で計算する。
規約：入力 y の正則性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実商同型の入力。 -/
theorem principalDPRelationIdeal_map_ringEquiv (e : A ≃+* B) (y : A) :
    principalDPRelationIdeal (e y) =
      (principalDPRelationIdeal y).map (rankOneDPRingEquiv e).toRingHom := by
  rw [principalDPRelationIdeal, principalDPRelationIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  congr 1
  change DividedPowerAlgebra.dp B 1 (1 : B) - algebraMap B _ (e y) =
    rankOneDPRingMap e.toRingHom (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A _ y)
  rw [map_sub, rankOneDPRingMap_dp, rankOneDPRingMap_coeff]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]

/-- 概要：係数環同型は γ₁=y の一次関係商の実環同型を誘導する。
方針：自由分冪代数の同型と一次関係イデアルの像の計算を商同型に渡す。
規約：これは通常環同型であり、分冪構造は別途移す。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数商上の pd 包への移送。 -/
def principalDPRingEquiv (e : A ≃+* B) (y : A) :
    PrincipalDPPresentation A y ≃+* PrincipalDPPresentation B (e y) :=
  Ideal.quotientEquiv _ _ (rankOneDPRingEquiv e) (principalDPRelationIdeal_map_ringEquiv e y)

/-- 概要：一次関係商の係数同型は元の係数を対応させる。
方針：商同型の代表元公式と自由分冪同型の係数公式を使う。
規約：標準係数射をそのまま使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数上の互換性。 -/
theorem principalDPRingEquiv_coeff (e : A ≃+* B) (y a : A) :
    principalDPRingEquiv e y (algebraMap A _ a) = algebraMap B _ (e a) := by
  change principalDPRingEquiv e y (Ideal.Quotient.mk _ (algebraMap A _ a)) = _
  rw [principalDPRingEquiv, Ideal.quotientEquiv_mk, rankOneDPRingEquiv_coeff]
  rfl

/-- 概要：一次関係商の係数同型は標準生成元を同じ次数の標準生成元へ送る。
方針：商同型の代表元公式と自由分冪の生成元公式を使う。
規約：入力元は係数同型で送る。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪構造の標準値の移送。 -/
theorem principalDPRingEquiv_generator (e : A ≃+* B) (y : A) (n : ℕ) :
    principalDPRingEquiv e y (principalDPGenerator y n) = principalDPGenerator (e y) n := by
  change principalDPRingEquiv e y (Ideal.Quotient.mk _ (DividedPowerAlgebra.dp A n (1 : A))) = _
  rw [principalDPRingEquiv, Ideal.quotientEquiv_mk, rankOneDPRingEquiv_dp]
  rfl


/-- 概要：係数同型が入力 y を指定した z へ送れば、それらの一次関係商は環同型。
方針：入力の等式で標準の係数同型比較を移す。
規約：入力の像の等式を明示する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の異なる具体的な剰余表示の同定。 -/
def principalDPRingEquivOfEq (e : A ≃+* B) (y : A) (z : B) (hy : e y = z) :
    PrincipalDPPresentation A y ≃+* PrincipalDPPresentation B z := by
  subst z
  exact principalDPRingEquiv e y

/-- 概要：入力像の等式を使った商同型も元の係数を係数同型で送る。
方針：入力像の等式で標準の係数公式へ帰着する。
規約：係数環射の値を明示する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の移送した分冪構造の入力値。 -/
theorem principalDPRingEquivOfEq_coeff (e : A ≃+* B) (y : A) (z : B) (hy : e y = z) (a : A) :
    principalDPRingEquivOfEq e y z hy (algebraMap A _ a) = algebraMap B _ (e a) := by
  subst z
  exact principalDPRingEquiv_coeff e y a

/-- 概要：入力像の等式を使った商同型は全標準生成元を同じ次数へ送る。
方針：入力像の等式で標準の生成元公式へ帰着する。
規約：全ての n を含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正次数イデアルと分冪値の比較。 -/
theorem principalDPRingEquivOfEq_generator (e : A ≃+* B) (y : A) (z : B) (hy : e y = z) (n : ℕ) :
    principalDPRingEquivOfEq e y z hy (principalDPGenerator y n) = principalDPGenerator z n := by
  subst z
  exact principalDPRingEquiv_generator e y n

end SerrePositivity.BhattScholze.Andre

end PrincipalDPRingEquiv

/-! ## p 局所・p 正則環の分冪構造の mod p 降下

## 概要

p 局所かつ p 正則な環の分冪イデアルが p を含めば、(p) は分冪で保たれ、
その分冪構造は mod p 商へ降りる。BS 著者版 Remark 7.15(1)（著者版 p.62）の
階乗部分環の剰余から実分冪構造を構成するための補題。

## 方針

n! の p 付値が正の n より小さいことと階乗恒等式により、γₙ(p) の p 可除性を得る。
生成イデアルの分冪安定性と既存の商の分冪 API を使う。

## 規約

係数環に分冪構造そのものを明示引数として与える。新たな引用は使わない。

## 使われ方

階乗部分環の大きい分冪イデアルを mod p へ降ろし、正次数イデアルの像へ制限する。
-/

@[expose] public noncomputable section PrimeDividedPowerQuotient

namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
variable {I : Ideal A} (H : DividedPowers I)

/-- 概要：p 正則・p 局所環の分冪イデアル内の p の正次数分冪は p で割り切れる。
方針：階乗の p 冪因子を正則性で消去し、残りの単元因子を除く。
規約：分冪イデアルへの p の所属を明示する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪構造の剰余への降下。 -/
theorem dividedPower_prime_dvd
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I)
    (n : ℕ) (hn : n ≠ 0) : (p : A) ∣ H.dpow n (p : A) := by
  obtain ⟨k, m, hm, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.factorial_ne_zero n) p (Fact.out : p.Prime).ne_one
  have hm0 : m ≠ 0 := fun hm0 => hm (hm0 ▸ dvd_zero p)
  have hk : padicValNat p n.factorial = k := by
    rw [hfac, padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have hkn : k < n := hk ▸ padicValNat_factorial_lt_of_ne_zero p hn
  have hr : IsLeftRegular (p : A) := hpA
  have he : (m : A) * H.dpow n (p : A) = (p : A) ^ (n - k) := by
    apply hr.pow k
    calc
      (p : A) ^ k * ((m : A) * H.dpow n (p : A)) =
          (n.factorial : A) * H.dpow n (p : A) := by
            rw [hfac, Nat.cast_mul, Nat.cast_pow, mul_assoc]
      _ = (p : A) ^ n := H.factorial_mul_dpow_eq_pow hpI
      _ = (p : A) ^ k * (p : A) ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkn.le]
  obtain ⟨v, hv⟩ := hlocal m hm
  have he' : H.dpow n (p : A) = (v⁻¹ : Aˣ) * (p : A) ^ (n - k) := by
    rw [← he, ← hv]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  rw [he']
  exact dvd_mul_of_dvd_right (dvd_pow_self (p : A) (Nat.sub_ne_zero_of_lt hkn)) _

/-- 概要：p を含む分冪イデアル内では (p) は分冪で保たれる。
方針：主イデアルの分冪安定性を生成元 p 上で確認する。
規約：p 正則性と p 局所性を前提に残す。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の mod p 分冪商の入力。 -/
theorem dividedPower_span_prime_isSubDPIdeal
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I) :
    H.IsSubDPIdeal (Ideal.span {(p : A)}) := by
  apply (H.span_isSubDPIdeal_iff (Set.singleton_subset_iff.mpr hpI)).mpr
  intro n hn s hs
  rcases hs with rfl
  exact Ideal.mem_span_singleton.mpr (dividedPower_prime_dvd p H hpA hlocal hpI n hn)

/-- 概要：p を含む分冪イデアルの構造は実 mod p 商へ降りる。
方針：(p) の分冪安定性から商 API に必要な交わりの安定性を得る。
規約：対象イデアルは元の分冪イデアルの商への像そのもの。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正標数の実分冪構造。 -/
def dividedPowerModPrime
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I) :
    DividedPowers (I.map (Ideal.Quotient.mk (Ideal.span {(p : A)}))) := by
  have hsub := dividedPower_span_prime_isSubDPIdeal p H hpA hlocal hpI
  apply DividedPowers.Quotient.dividedPowers H
  simpa only [inf_eq_left.mpr hsub.isSubideal] using hsub

/-- 概要：mod p の分冪作用は元の分冪値を標準商射で送った値に一致する。
方針：商分冪構造の評価公式を適用する。
規約：元は元の分冪イデアル内に取る。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の階乗生成元の剰余の照合。 -/
theorem dividedPowerModPrime_apply
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I)
    (n : ℕ) {a : A} (ha : a ∈ I) :
    (dividedPowerModPrime p H hpA hlocal hpI).dpow n
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) a) =
      Ideal.Quotient.mk _ (H.dpow n a) := by
  exact DividedPowers.Quotient.dpow_apply H
    (by
      have hsub := dividedPower_span_prime_isSubDPIdeal p H hpA hlocal hpI
      simpa only [inf_eq_left.mpr hsub.isSubideal] using hsub) ha


/-- 概要：標準 mod p 商射は分冪射である。
方針：商分冪構造の射の互換性を使う。
規約：元の分冪イデアルとその実像を比較する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正次数イデアルの像への制限。 -/
theorem dividedPowerModPrime_isDPMorphism
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I) :
    H.IsDPMorphism (dividedPowerModPrime p H hpA hlocal hpI)
      (Ideal.Quotient.mk (Ideal.span {(p : A)})) := by
  exact DividedPowers.Quotient.isDPMorphism H
    (by
      have hsub := dividedPower_span_prime_isSubDPIdeal p H hpA hlocal hpI
      simpa only [inf_eq_left.mpr hsub.isSubideal] using hsub)

end SerrePositivity.BhattScholze.Andre

end PrimeDividedPowerQuotient

/-! ## 階乗部分環の正次数イデアルの実 mod p 分冪構造

## 概要

p 局所 δ 係数環の階乗部分環を mod p に還元した環で、正次数の階乗生成元の
像のイデアルに実際の分冪構造を構成する。BS 著者版 Remark 7.15(1)（著者版 p.62）。

## 方針

大きい p 除算可能イデアルの分冪構造を mod p に降ろし、正次数イデアルの像へ制限する。

## 規約

係数環の p 正則性や入力元の正則性はこの段階では不要。
階乗部分環自体の p 正則性を使用する。

## 使われ方

正則一元入力では既存の実 mod p 比較で一次関係商へ移し、実 pd 包と比較する。
-/

@[expose] public noncomputable section FactorialModPrimeDividedPowers

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A)
local notation "S" => pDivisionFactorialSubring p y
local notation "E" => pDivisionFactorialDelta hlocal D y
local notation "H" => pDivisionFactorialDividedPowers hlocal D y
local notation "q" => Ideal.Quotient.mk (Ideal.span {(p : S)})

include hlocal in
omit [Fact p.Prime] in
/-- 概要：階乗部分環も p 局所である。
方針：元の係数環の単元を標準基底射で送る。
規約：p と互いに素な自然数を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の mod p 分冪降下への入力。 -/
theorem factorialSubring_primeLocal (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : S) := by
  simpa only [map_natCast] using (hlocal m hm).map (pDivisionFactorialBase p y)

/-- 概要：階乗部分環の p は大きい p 除算可能イデアルに属する。
方針：p がその p 乗を割ることを使う。
規約：正次数の階乗イデアルに p の所属を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の大きいイデアルからの降下。 -/
theorem factorialSubring_prime_mem : (p : S) ∈ (E).primeDividedPowerIdeal :=
  ((E).mem_primeDividedPowerIdeal _).mpr (dvd_pow_self _ (Fact.out : p.Prime).ne_zero)

/-- 概要：階乗部分環の大きい分冪構造は実 mod p 商へ降りる。
方針：階乗部分環の p 正則性・p 局所性と p の所属を一般降下補題へ渡す。
規約：対象は大きい分冪イデアルの標準商への実像。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正次数への制限の出発点。 -/
def factorialModPrimeAmbientDividedPowers :
    DividedPowers ((E).primeDividedPowerIdeal.map q) :=
  dividedPowerModPrime p H (pDivisionFactorial_p_mul_injective y)
    (factorialSubring_primeLocal hlocal y) (factorialSubring_prime_mem hlocal D y)

/-- 概要：mod p 正次数イデアルは、大きい分冪イデアル内で分冪に安定。
方針：元の正次数イデアルの安定性を分冪商射で送る。
規約：正次数イデアルの像をそのまま使い、飽和性を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正次数分冪構造の構成。 -/
theorem factorialModPrimeIdeal_isSubDPIdeal :
    (factorialModPrimeAmbientDividedPowers hlocal D y).IsSubDPIdeal
      ((pDivisionFactorialIdeal p y).map q) :=
  DividedPowers.isSubDPIdeal_map_of_isSubDPIdeal
    (dividedPowerModPrime_isDPMorphism p H (pDivisionFactorial_p_mul_injective y)
      (factorialSubring_primeLocal hlocal y) (factorialSubring_prime_mem hlocal D y))
    (pDivisionFactorialIdeal_isSubDPIdeal hlocal D y)

/-- 概要：正次数の階乗イデアルの mod p 像には実際の分冪構造がある。
方針：大きい商分冪構造を分冪安定な正次数イデアルの像へ制限する。
規約：入力元の正則性と係数環の p 正則性は要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正標数での実分冪構造。 -/
def factorialModPrimeDividedPowers : DividedPowers ((pDivisionFactorialIdeal p y).map q) := by
  classical
  exact DividedPowers.IsSubDPIdeal.dividedPowers (factorialModPrimeAmbientDividedPowers hlocal D y)
    (factorialModPrimeIdeal_isSubDPIdeal hlocal D y)

/-- 概要：mod p の正次数分冪は元の大きい分冪作用の商像と一致する。
方針：正次数への制限と商分冪作用の二つの評価公式を使う。
規約：元を元の正次数イデアル内に取る。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の階乗生成元の比較。 -/
theorem factorialModPrimeDividedPowers_apply (n : ℕ) {a : S}
    (ha : a ∈ pDivisionFactorialIdeal p y) :
    (factorialModPrimeDividedPowers hlocal D y).dpow n (q a) = q ((H).dpow n a) := by
  classical
  rw [factorialModPrimeDividedPowers, DividedPowers.IsSubDPIdeal.dpow_eq_of_mem _ _
    (Ideal.mem_map_of_mem q ha)]
  exact dividedPowerModPrime_apply p H (pDivisionFactorial_p_mul_injective y)
    (factorialSubring_primeLocal hlocal y) (factorialSubring_prime_mem hlocal D y) n
    ((pDivisionFactorialIdeal_isSubDPIdeal hlocal D y).isSubideal ha)

/-- 概要：基底元 y_s の mod p 像の n 次分冪は n 次階乗生成元の mod p 像。
方針：降下前の具体的な階乗値の公式を商へ移す。
規約：n=0 も含める。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 包の標準生成元の照合。 -/
theorem factorialModPrimeDividedPowers_base_apply (s : σ) (n : ℕ) :
    (factorialModPrimeDividedPowers hlocal D y).dpow n
      (q (pDivisionFactorialBase p y (y s))) =
      q (⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ : S) := by
  rw [factorialModPrimeDividedPowers_apply hlocal D y n
    (pDivisionFactorialBase_mem_factorialIdeal y s)]
  congr 1
  apply Subtype.ext
  exact pDivisionFactorialDividedPowers_base_apply hlocal D y s n

end SerrePositivity.BhattScholze.Andre

end FactorialModPrimeDividedPowers

/-! ## 標数 p の一元分冪代数の素数次数シフト

## 概要

p が零となる係数環上の一元分冪代数には γₙ を γₚₙ へ送る係数代数射がある。
その反復により、各 γₚⁱ の p 乗は零となる。
BS 著者版 Remark 7.15(1)（著者版 p.62）の切断多項式表示の関係式の計算。

## 方針

具体的な分冪基底から線形写像を定める。二項係数の Lucas 合同により積を保存する。
一次分冪生成元の p 乗消滅をこの代数射で順に移す。

## 規約

p は素数とする。係数環の非零性や CharP の型クラスは要求せず、p=0 を明示する。
実 pd 包や prismatic envelope の同定は別工程。

## 使われ方

可算個の切断変数を分冪代数へ評価する射の関係式を供給する。
-/

@[expose] public noncomputable section DividedPowerPrimeShift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "DA" => DividedPowerAlgebra A A
local notation "b" => rankOneDPAnyBasis A

omit [Fact p.Prime] in
/-- 概要：p が零となる環では、p に関する自然数の合同は係数環内の等式を与える。
方針：両自然数を剰余と p 倍に分ける。
規約：零環を含め、CharP のインスタンスを要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の Lucas 合同による積の照合。 -/
theorem natCast_eq_of_modEq_of_prime_zero (hp : (p : A) = 0) {m n : ℕ}
    (h : Nat.ModEq p m n) : (m : A) = (n : A) := by
  have hc (k : ℕ) : (k : A) = (k % p : ℕ) := by
    have he := congrArg (Nat.cast : ℕ → A) (Nat.mod_add_div k p)
    simpa only [Nat.cast_add, Nat.cast_mul, hp, zero_mul, add_zero] using he.symm
  exact (hc m).trans ((congrArg (Nat.cast : ℕ → A) h).trans (hc n).symm)

/-- 概要：標準分冪基底の次数を p 倍する係数線形写像。
方針：具体的基底からの線形写像の普遍性を使う。
規約：線形写像の定義自体には標数条件を使わない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の素数冪生成元。 -/
def dividedPowerPrimeShiftLinear : DA →ₗ[A] DA :=
  (b).constr A (fun n => DividedPowerAlgebra.dp A (p * n) (1 : A))

omit [Fact p.Prime] in
/-- 概要：次数シフト線形写像は γₙ を γₚₙ に送る。
方針：基底から定めた線形写像の基底上の公式を使う。
規約：標数条件は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の積の計算。 -/
theorem dividedPowerPrimeShiftLinear_dp (n : ℕ) :
    dividedPowerPrimeShiftLinear (A := A) p (DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp A (p * n) (1 : A) := by
  simpa only [dividedPowerPrimeShiftLinear, rankOneDPAnyBasis_apply] using
    (b).constr_basis A (fun k => DividedPowerAlgebra.dp A (p * k) (1 : A)) n

/-- 概要：p が係数環内で零なら次数シフトは積を保存する。
方針：双線形写像を分冪基底上で比較し、Lucas の二項係数合同を使う。
規約：係数環の非零性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断生成元への代数射。 -/
theorem dividedPowerPrimeShiftLinear_mul (hp : (p : A) = 0) (x y : DA) :
    dividedPowerPrimeShiftLinear p (x * y) =
      dividedPowerPrimeShiftLinear p x * dividedPowerPrimeShiftLinear p y := by
  let L := dividedPowerPrimeShiftLinear (A := A) p
  have hpD : (p : DA) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A DA) hp
  have hmul : (LinearMap.mul A DA).compr₂ L = (LinearMap.mul A DA).compl₁₂ L L := by
    apply (b).ext
    intro m
    apply (b).ext
    intro n
    change L ((b) m * (b) n) = L ((b) m) * L ((b) n)
    dsimp only [L]
    simp only [rankOneDPAnyBasis_apply, DividedPowerAlgebra.dp_mul, map_nsmul,
      dividedPowerPrimeShiftLinear_dp]
    have hc : (((p * (m + n)).choose (p * m) : ℕ) : DA) = ((m + n).choose m : ℕ) :=
      natCast_eq_of_modEq_of_prime_zero p hpD Choose.choose_mul_mul_modEq_choose_nat
    simp only [← Nat.mul_add]
    rw [nsmul_eq_mul, nsmul_eq_mul, hc]
  exact congrArg (fun f : DA →ₗ[A] DA →ₗ[A] DA => f x y) hmul

/-- 概要：標数 p の次数シフトを係数代数射として束ねる。
方針：線形写像の積保存、零次分冪と係数スカラーの保存を使う。
規約：係数環の p=0 を明示する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の素数冪次数の関係式。 -/
def dividedPowerPrimeShift (hp : (p : A) = 0) : DA →ₐ[A] DA where
  toFun := dividedPowerPrimeShiftLinear (A := A) p
  map_zero' := map_zero (dividedPowerPrimeShiftLinear (A := A) p)
  map_add' := map_add (dividedPowerPrimeShiftLinear (A := A) p)
  map_one' := by
    simpa only [Nat.mul_zero, DividedPowerAlgebra.dp_zero] using
      dividedPowerPrimeShiftLinear_dp (A := A) p 0
  map_mul' := dividedPowerPrimeShiftLinear_mul p hp
  commutes' a := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    have h1 : dividedPowerPrimeShiftLinear p (1 : DA) = 1 := by
      simpa only [Nat.mul_zero, DividedPowerAlgebra.dp_zero] using
        dividedPowerPrimeShiftLinear_dp (A := A) p 0
    rw [h1]

/-- 概要：次数シフト代数射も、標準分冪生成元の次数を p 倍する。
方針：元の線形写像の公式を使う。
規約：係数環内で p は零。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の素数冪生成元の反復。 -/
theorem dividedPowerPrimeShift_dp (hp : (p : A) = 0) (n : ℕ) :
    dividedPowerPrimeShift p hp (DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp A (p * n) (1 : A) :=
  dividedPowerPrimeShiftLinear_dp p n

/-- 概要：素数冪次数の分冪生成元 γₚⁿ の p 乗は零。
方針：一次生成元の p 乗消滅を次数シフト代数射で帰納的に移す。
規約：係数環の非零性を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の gᵢᵖ=0 の具体的関係。 -/
theorem dividedPowerPrimePower_pow_zero (hp : (p : A) = 0) (n : ℕ) :
    DividedPowerAlgebra.dp A (p ^ n) (1 : A) ^ p = 0 := by
  induction n with
  | zero =>
      simpa only [pow_zero] using rankOneDPGenerator_pow_eq_zero (Fact.out : p.Prime).pos hp
  | succ n ih =>
      have h := congrArg (dividedPowerPrimeShift p hp) ih
      rw [map_pow, dividedPowerPrimeShift_dp, map_zero] at h
      simpa only [pow_succ'] using h

/-- 概要：素数次数のシフト線形写像は単射。
方針：標準分冪基底の線形独立性を、単射な指数写像 n↦pn に沿って制限する。
規約：この単射性には係数環内の p=0 は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断多項式表示の独立性の準備。 -/
theorem dividedPowerPrimeShiftLinear_injective :
    Function.Injective (dividedPowerPrimeShiftLinear (A := A) p) := by
  have hi : Function.Injective (fun n : ℕ => p * n) := by
    intro m n h
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos h
  change Function.Injective ((b).constr A
    (fun n => DividedPowerAlgebra.dp A (p * n) (1 : A)))
  apply (b).injective_constr_of_linearIndependent
  simpa only [rankOneDPAnyBasis_apply, Function.comp_def] using (b).linearIndependent.comp _ hi

/-- 概要：標数 p の素数次数シフト代数射は単射。
方針：同じ台写像の係数線形単射性を使う。
規約：係数環の非零性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の素数冪生成元の独立性。 -/
theorem dividedPowerPrimeShift_injective (hp : (p : A) = 0) :
    Function.Injective (dividedPowerPrimeShift (A := A) p hp) :=
  dividedPowerPrimeShiftLinear_injective p

end SerrePositivity.BhattScholze.Andre

end DividedPowerPrimeShift

/-! ## 分冪代数の最初の切断変数と次数シフトによるテンソル分解

## 概要

p が零となる係数環 A 上の一元分冪代数は、切断多項式環 A[X]/(Xᵖ) と
同じ分冪代数の A 上のテンソル積に同型である。
写像は c⊗d を c(γ₁) と次数シフト(d) の積に送る。
BS 著者版 Remark 7.15(1)（著者版 p.62）の可算切断多項式表示の一段の分解。

## 方針

標準冪基底と分冪基底のテンソル基底が、既存の次数ブロック基底へ写ることを示す。
零係数環は両辺の自明性で扱う。

## 規約

p は素数、p=0 を係数環内の等式として明示する。係数環の非零性は要求しない。
これは通常の代数同型であり、prismatic Frobenius との同定は含まない。

## 使われ方

切断多項式評価の有限段の独立性を帰納的に示すために使う。
-/

@[expose] public noncomputable section DividedPowerPrimeTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "DA" => DividedPowerAlgebra A A
local notation "C" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "hprime" => (Fact.out : p.Prime)

/-- 概要：最初の切断変数と次数シフト側の積によるテンソル評価射。
方針：切断多項式の標準評価と次数シフト代数射をテンソルの普遍性で合成する。
規約：元の係数環 A の作用を保つ。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断表示の一段の分解。 -/
def dividedPowerPrimeTensorMap (hp : (p : A) = 0) : C ⊗[A] DA →ₐ[A] DA :=
  Algebra.TensorProduct.lift (rankOneDPTruncatedMap (hprime).pos hp)
    (dividedPowerPrimeShift p hp) (fun _ _ => Commute.all _ _)

/-- 概要：テンソル評価射の純テンソル上の値は指定した二つの像の積。
方針：テンソル代数射の評価公式を使う。
規約：次数シフトは通常の Frobenius とは区別する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の基底上の計算。 -/
theorem dividedPowerPrimeTensorMap_tmul (hp : (p : A) = 0) (c : C) (d : DA) :
    dividedPowerPrimeTensorMap p hp (c ⊗ₜ[A] d) =
      rankOneDPTruncatedMap (hprime).pos hp c * dividedPowerPrimeShift p hp d := rfl

/-- 概要：テンソル評価射は零係数環を含めて全単射。
方針：非零枝ではテンソル基底を次数ブロック基底に送る線形同型と比較する。
規約：非零性は結論の前提に残さない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の可算切断表示の独立性。 -/
theorem dividedPowerPrimeTensorMap_bijective (hp : (p : A) = 0) :
    Function.Bijective (dividedPowerPrimeTensorMap (A := A) p hp) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := hA
    let : Subsingleton DA := Module.subsingleton A DA
    let : Subsingleton (C ⊗[A] DA) := Module.subsingleton A _
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  · let := hA
    let b0 := (rankOneDPTruncatedBasis p A).tensorProduct (rankOneDPAnyBasis A)
    let b1 := (rankOneDPPrimeBlockBasis hprime hp).reindex (Equiv.prodComm ℕ (Fin p))
    let e := b0.equiv b1 (Equiv.refl (Fin p × ℕ))
    have he : (dividedPowerPrimeTensorMap (A := A) p hp).toLinearMap = e.toLinearMap := by
      apply b0.ext
      rintro ⟨r, k⟩
      simp only [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
      dsimp only [e]
      rw [Module.Basis.equiv_apply]
      dsimp [b0, b1]
      rw [Module.Basis.tensorProduct_apply, Module.Basis.reindex_apply]
      change dividedPowerPrimeTensorMap p hp
        (rankOneDPTruncatedBasis p A r ⊗ₜ[A] rankOneDPAnyBasis A k) =
          rankOneDPPrimeBlockBasis hprime hp (k, r)
      rw [dividedPowerPrimeTensorMap_tmul, rankOneDPTruncatedMap_basis,
        rankOneDPAnyBasis_apply, dividedPowerPrimeShift_dp, rankOneDPPrimeBlockBasis_apply]
    change Function.Bijective (dividedPowerPrimeTensorMap (A := A) p hp).toLinearMap
    rw [he]
    exact e.bijective

/-- 概要：一元分冪代数は最初の切断多項式環と次数シフト側のテンソル積に同型。
方針：具体的な全単射代数射を代数同型として束ねる。
規約：両辺の元の A 作用を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断変数を一つずつ分ける帰納。 -/
def dividedPowerPrimeTensorEquiv (hp : (p : A) = 0) : C ⊗[A] DA ≃ₐ[A] DA :=
  AlgEquiv.ofBijective (dividedPowerPrimeTensorMap p hp) (dividedPowerPrimeTensorMap_bijective p hp)

/-- 概要：テンソル同型の順射は指定した二つの像の積を与える。
方針：全単射代数射から作った同型の台写像の等式を使う。
規約：原典の切断変数の値を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の標準射の互換性。 -/
theorem dividedPowerPrimeTensorEquiv_tmul (hp : (p : A) = 0) (c : C) (d : DA) :
    dividedPowerPrimeTensorEquiv p hp (c ⊗ₜ[A] d) =
      rankOneDPTruncatedMap (hprime).pos hp c * dividedPowerPrimeShift p hp d := rfl

end SerrePositivity.BhattScholze.Andre

end DividedPowerPrimeTensor

/-! ## 有限切断テンソル段の分冪評価

## 概要

切断多項式環 A[X]/(Xᵖ) の有限反復テンソル積を一元分冪代数へ単射に写す。
BS 著者版 Remark 7.15(1)（著者版 p.62）の可算切断表示の有限段である。

## 方針

最初の切断変数を分けるテンソル同型と、モニック商の自由性による
テンソル化の単射性保存を反復する。

## 規約

係数環 A は可換環、p は素数で A 内で零とする。零環も含む。
有限段の束には標準の CommAlgCat を用い、係数環作用を保持する。

## 使われ方

可算多項式の有限変数支持に制限した評価の単射性へ接続する。
-/

@[expose] public noncomputable section DividedPowerPrimeFiniteTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "DA" => DividedPowerAlgebra A A
local notation "C" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)

/-- 概要：分冪代数への単射を切断変数一つを加えた単射へ拡張する。
方針：モニック商の自由性によるテンソル化と、次数シフトのテンソル分解を合成する。
規約：入力代数の平坦性を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の有限切断段の帰納。 -/
theorem dividedPowerPrimeTensorMap_comp_injective (hp : (p : A) = 0)
    {B : Type u} [CommRing B] [Algebra A B]
    (f : B →ₐ[A] DA) (hf : Function.Injective f) :
    Function.Injective ((dividedPowerPrimeTensorMap p hp).comp
      (Algebra.TensorProduct.map (AlgHom.id A C) f)) := by
  let : Module.Free A C := (Polynomial.monic_X.pow p).free_adjoinRoot
  have he : (Algebra.TensorProduct.map (AlgHom.id A C) f).toLinearMap =
      f.toLinearMap.lTensor C := by
    ext c b
    rfl
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id A C) f) := by
    change Function.Injective (Algebra.TensorProduct.map (AlgHom.id A C) f).toLinearMap
    rw [he]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hf
  exact (dividedPowerPrimeTensorMap_bijective p hp).injective.comp hinj

omit [Fact p.Prime] in
/-- 概要：n 個の切断変数を持つ有限反復テンソル段を係数代数として束ねる。
方針：零段を A、次段を A[X]/(Xᵖ) と前段のテンソル積にする。
規約：この定義には素数性や標数の仮定は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の有限変数支持の入れ物。 -/
def dividedPowerPrimeTensorStage : ℕ → CommAlgCat.{u} A
  | 0 => CommAlgCat.of A A
  | n + 1 => CommAlgCat.of A (C ⊗[A] dividedPowerPrimeTensorStage n)

/-- 概要：有限テンソル段から一元分冪代数への標準評価射。
方針：前段の評価をテンソル化し、最初の切断変数と次数シフトの積に送る。
規約：n 番目の変数に対応する次数は p の n 乗である。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の有限切断評価。 -/
def dividedPowerPrimeTensorStageEval (hp : (p : A) = 0) :
    (n : ℕ) → dividedPowerPrimeTensorStage (A := A) p n →ₐ[A] DA
  | 0 => Algebra.ofId A DA
  | n + 1 => (dividedPowerPrimeTensorMap p hp).comp
      (Algebra.TensorProduct.map (AlgHom.id A C) (dividedPowerPrimeTensorStageEval hp n))

/-- 概要：各有限テンソル段の標準分冪評価は単射。
方針：零段では標準分冪基底の係数埋込、次段では切断テンソル化の単射性保存を使う。
規約：係数環の非零性を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の可算表示を有限支持へ制限する。 -/
theorem dividedPowerPrimeTensorStageEval_injective (hp : (p : A) = 0) (n : ℕ) :
    Function.Injective (dividedPowerPrimeTensorStageEval (A := A) p hp n) := by
  induction n with
  | zero =>
    change Function.Injective (algebraMap A DA)
    intro a b hab
    have hone : (1 : DA) = rankOneDPAnyBasis A 0 := by
      rw [rankOneDPAnyBasis_apply, DividedPowerAlgebra.dp_zero]
    have h := congrArg (fun x : DA => (rankOneDPAnyBasis A).repr x 0) hab
    simpa [Algebra.algebraMap_eq_smul_one, hone] using h
  | succ n ih =>
    exact dividedPowerPrimeTensorMap_comp_injective p hp _ ih


omit [Fact p.Prime] in
/-- 概要：有限テンソル段の i 番目の切断変数。
方針：最初の変数は左因子の根、後続は右因子の変数として再帰する。
規約：番号は Fin n であり、零段に変数はない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の多項式変数との照合。 -/
def dividedPowerPrimeTensorStageRoot :
    (n : ℕ) → Fin n → dividedPowerPrimeTensorStage (A := A) p n
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases
      (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ⊗ₜ[A] 1)
      (fun j => 1 ⊗ₜ[A] dividedPowerPrimeTensorStageRoot n j) i

omit [Fact p.Prime] in
/-- 概要：有限テンソル段の変数は p 乗が零。
方針：左因子の根の関係式と右因子の帰納仮定を純テンソルの冪へ適用する。
規約：この消滅自体には標数や素数性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断多項式商からの射の構成。 -/
theorem dividedPowerPrimeTensorStageRoot_pow (n : ℕ) (i : Fin n) :
    dividedPowerPrimeTensorStageRoot (A := A) p n i ^ p = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ⊗ₜ[A]
        (1 : dividedPowerPrimeTensorStage (A := A) p n)) ^ p = 0
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
      have hroot : AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ^ p = 0 := by
        simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using
          AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial A) ^ p)
      rw [hroot, TensorProduct.zero_tmul]
    · change ((1 : C) ⊗ₜ[A] dividedPowerPrimeTensorStageRoot p n j) ^ p = 0
      rw [Algebra.TensorProduct.tmul_pow, one_pow, ih j, TensorProduct.tmul_zero]

/-- 概要：有限段の i 番目の変数の分冪評価は γₚⁱ。
方針：最初の変数の評価と、次数シフトによる添字の p 倍を帰納する。
規約：切断変数の番号をそのまま素数冪の指数に使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の標準多項式評価との比較。 -/
theorem dividedPowerPrimeTensorStageEval_root (hp : (p : A) = 0) (n : ℕ) (i : Fin n) :
    dividedPowerPrimeTensorStageEval p hp n (dividedPowerPrimeTensorStageRoot p n i) =
      DividedPowerAlgebra.dp A (p ^ (i : ℕ)) (1 : A) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change dividedPowerPrimeTensorMap p hp
        (Algebra.TensorProduct.map (AlgHom.id A C) (dividedPowerPrimeTensorStageEval p hp n)
          (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ⊗ₜ[A] 1)) = _
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one,
        dividedPowerPrimeTensorMap_tmul, rankOneDPTruncatedMap_root, mul_one,
        Fin.val_zero, pow_zero]
    · change dividedPowerPrimeTensorMap p hp
        (Algebra.TensorProduct.map (AlgHom.id A C) (dividedPowerPrimeTensorStageEval p hp n)
          (1 ⊗ₜ[A] dividedPowerPrimeTensorStageRoot p n j)) = _
      simp only [Algebra.TensorProduct.map_tmul, ih,
        dividedPowerPrimeTensorMap_tmul, map_one, one_mul, dividedPowerPrimeShift_dp,
        Fin.val_succ, pow_succ']

end SerrePositivity.BhattScholze.Andre

end DividedPowerPrimeFiniteTensor

/-! ## 有限切断テンソル段の普遍性

## 概要

有限テンソル段からの係数代数射は、p 乗が零となる n 個の元の選択と対応する。
BS 著者版 Remark 7.15(1)（著者版 p.62）の切断多項式表示の有限版。

## 方針

AdjoinRoot とテンソル積の普遍性を反復し、変数上の値による外延性を示す。

## 規約

p は任意の自然数。普遍性自体には素数性・標数・非零性は不要。

## 使われ方

有限切断多項式商と有限テンソル段を同定して標準評価の単射性へ進む。
-/

@[expose] public noncomputable section DividedPowerPrimeFiniteUniversal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
variable {A : Type u} [CommRing A] (p : ℕ)
variable {B : Type u} [CommRing B] [Algebra A B]
local notation "C" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)

/-- 概要：p 乗が零となる元の有限族への指定値から有限テンソル段の射を作る。
方針：最初の元に AdjoinRoot の普遍射、残りに帰納的な普遍射を使いテンソルから延長する。
規約：全射性や単射性をこの射の前提にしない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断変数の普遍性。 -/
def dividedPowerPrimeTensorStageLift : (n : ℕ) → (b : Fin n → B) →
    (∀ i, b i ^ p = 0) → dividedPowerPrimeTensorStage (A := A) p n →ₐ[A] B
  | 0, _, _ => Algebra.ofId A B
  | n + 1, b, hb => Algebra.TensorProduct.lift
      (AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial A) ^ p) (Algebra.ofId A B)
        (b 0) (by simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using hb 0))
      (dividedPowerPrimeTensorStageLift n (fun i => b i.succ) (fun i => hb i.succ))
      (fun _ _ => Commute.all _ _)

/-- 概要：有限テンソル段の普遍射は各変数を指定した元へ送る。
方針：純テンソルの評価と AdjoinRoot の根の評価を帰納する。
規約：変数の番号を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の多項式表示の逆射。 -/
theorem dividedPowerPrimeTensorStageLift_root (n : ℕ) (b : Fin n → B)
    (hb : ∀ i, b i ^ p = 0) (i : Fin n) :
    dividedPowerPrimeTensorStageLift (A := A) p n b hb
      (dividedPowerPrimeTensorStageRoot (A := A) p n i) =
      b i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    let f0 : C →ₐ[A] B := AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial A) ^ p)
      (Algebra.ofId A B) (b 0)
      (by simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using hb 0)
    let f1 := dividedPowerPrimeTensorStageLift (A := A) p n
      (fun j => b j.succ) (fun j => hb j.succ)
    refine Fin.cases ?_ (fun j => ?_) i
    · change f0 (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p)) * f1 1 = b 0
      rw [map_one, mul_one]
      exact AdjoinRoot.lift_root (i := algebraMap A B)
        (by simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using hb 0)
    · change f0 1 * f1 (dividedPowerPrimeTensorStageRoot (A := A) p n j) = b j.succ
      rw [map_one, one_mul]
      exact ih _ _ j

/-- 概要：有限テンソル段からの係数代数射は全変数上の値で一意に決まる。
方針：左因子では根の外延性、右因子では前段の変数の外延性を使う。
規約：終域は任意の可換係数代数。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の有限切断表示の同型の検証。 -/
theorem dividedPowerPrimeTensorStageHom_ext (n : ℕ)
    (f g : dividedPowerPrimeTensorStage (A := A) p n →ₐ[A] B)
    (h : ∀ i, f (dividedPowerPrimeTensorStageRoot (A := A) p n i) =
      g (dividedPowerPrimeTensorStageRoot (A := A) p n i)) : f = g := by
  induction n with
  | zero =>
    apply AlgHom.ext
    intro a
    exact (f.commutes a).trans (g.commutes a).symm
  | succ n ih =>
    apply Algebra.TensorProduct.ext
    · apply AdjoinRoot.algHom_ext
      exact h 0
    · apply ih
      intro i
      exact h i.succ

end SerrePositivity.BhattScholze.Andre

end DividedPowerPrimeFiniteUniversal

/-! ## 素数冪分冪生成元と切断変数からの全射

## 概要

標数 p の一元分冪代数は全 γₚⁿ で係数代数として生成される。
各生成元の p 乗が零となることから、可算個の切断変数の多項式商から標準全射がある。
BS 著者版 Remark 7.15(1)（著者版 p.62）の具体的表示への入力。

## 方針

次数シフトが生成部分代数を保つことと、次数の p 進商・剰余を使う強帰納を用いる。
p 未満の階乗が単元であることから、全ての標準分冪を生成する。

## 規約

ここでは切断変数からの全射までを示す。単射性や実 pd 包との同定は含まない。
係数環の非零性は不要。

## 使われ方

切断多項式表示の同型を構成する際の標準射と全射性を供給する。
-/

@[expose] public noncomputable section DividedPowerPrimeGenerators

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "DA" => DividedPowerAlgebra A A
local notation "S" => Algebra.adjoin A
  (Set.range fun n : ℕ => DividedPowerAlgebra.dp A (p ^ n) (1 : A))

/-- 概要：素数冪次数の分冪で生成した部分代数は次数シフトで保たれる。
方針：生成元・係数・和・積について確認する。
規約：標準次数シフト代数射を使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の全分冪の生成の帰納。 -/
theorem dividedPowerPrimeShift_mem_adjoin (hp : (p : A) = 0) {x : DA} (hx : x ∈ S) :
    dividedPowerPrimeShift p hp x ∈ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      rw [dividedPowerPrimeShift_dp, ← pow_succ']
      exact Algebra.subset_adjoin (Set.mem_range_self (n + 1))
  | algebraMap a =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

/-- 概要：全ての標準分冪 γₙ は素数冪次数の分冪で生成した部分代数に属する。
方針：n の p による商・剰余と低次階乗の単元性を用いる強帰納。
規約：係数環の非零性を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断変数表示への全射性。 -/
theorem dividedPower_dp_mem_prime_adjoin (hp : (p : A) = 0) (n : ℕ) :
    DividedPowerAlgebra.dp A n (1 : A) ∈ S := by
  have hprime := (Fact.out : p.Prime)
  have h1 : DividedPowerAlgebra.dp A 1 (1 : A) ∈ S :=
    Algebra.subset_adjoin ⟨0, rfl⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simpa only [DividedPowerAlgebra.dp_zero] using (Subalgebra.one_mem S)
      · let k := n / p
        let r := n % p
        have hk : k < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hprime.one_lt
        have hr : r < p := Nat.mod_lt _ hprime.pos
        have he : p * k + r = n := by
          simpa only [k, r, Nat.mul_comm] using Nat.div_add_mod n p
        have hpk : DividedPowerAlgebra.dp A (p * k) (1 : A) ∈ S := by
          rw [← dividedPowerPrimeShift_dp p hp k]
          exact dividedPowerPrimeShift_mem_adjoin p hp (ih k hk)
        have hm := Subalgebra.mul_mem S (Subalgebra.pow_mem S h1 r) hpk
        rw [rankOneDPGenerator_pow_mul_prime_block hp, he] at hm
        have hs : (r.factorial : A) • DividedPowerAlgebra.dp A n (1 : A) ∈ (S).toSubmodule := by
          change (r.factorial : A) • DividedPowerAlgebra.dp A n (1 : A) ∈ S
          rw [Algebra.smul_def, map_natCast]
          exact hm
        exact ((S).toSubmodule.smul_mem_iff_of_isUnit
          (rankOneDPPrimeBlock_factorial_isUnit hprime hp hr)).mp hs

/-- 概要：標数 p の一元分冪代数は可算個の素数冪次数の分冪で生成される。
方針：全標準分冪の所属と、それらの係数線形生成を使う。
規約：部分代数の等式として述べる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断多項式射の全射性。 -/
theorem dividedPowerPrime_adjoin_eq_top (hp : (p : A) = 0) : S = ⊤ := by
  have hspan : Submodule.span A (Set.range fun n : ℕ =>
      DividedPowerAlgebra.dp A n (1 : A)) ≤ (S).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact dividedPower_dp_mem_prime_adjoin p hp n
  rw [rankOneDP_span_eq_top] at hspan
  apply top_unique
  intro x _hx
  exact hspan (Submodule.mem_top)

/-- 概要：可算個の変数の p 乗を零とする具体的多項式商。
方針：既存のモニック冪関係イデアルで全ての右辺を零にする。
規約：この定義自体には係数環の標数を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断多項式表示の台環。 -/
abbrev DividedPowerPrimeTruncatedAlgebra :=
  MvPolynomial ℕ A ⧸ monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0)

/-- 概要：各切断変数を対応する γₚⁿ へ送る標準係数代数射。
方針：各 γₚⁿ の p 乗消滅により、通常多項式評価射を商へ降ろす。
規約：この段階で単射性は主張しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の具体的切断多項式表示。 -/
def dividedPowerPrimeTruncatedEval (hp : (p : A) = 0) :
    DividedPowerPrimeTruncatedAlgebra (A := A) p →ₐ[A] DA := by
  let g : MvPolynomial ℕ A →ₐ[A] DA :=
    MvPolynomial.aeval (fun n : ℕ => DividedPowerAlgebra.dp A (p ^ n) (1 : A))
  apply Ideal.Quotient.liftₐ _ g
  intro f hf
  have hker : monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0) ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change g (MvPolynomial.X n ^ p - MvPolynomial.C (0 : A)) = 0
    simp [g, dividedPowerPrimePower_pow_zero p hp]
  exact hker hf

/-- 概要：標準評価射は n 番目の切断変数を γₚⁿ に送る。
方針：商からの評価射と多項式評価の定義を使う。
規約：変数の番号を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の生成元の照合。 -/
theorem dividedPowerPrimeTruncatedEval_X (hp : (p : A) = 0) (n : ℕ) :
    dividedPowerPrimeTruncatedEval p hp
      (Ideal.Quotient.mk _ (MvPolynomial.X n)) = DividedPowerAlgebra.dp A (p ^ n) (1 : A) := by
  simp [dividedPowerPrimeTruncatedEval]

/-- 概要：可算切断多項式商から一元分冪代数への標準評価射は全射。
方針：その像が全ての素数冪分冪生成元を含み、それらが全代数を生成することを使う。
規約：単射性は別工程であり、この結果を同型とは数えない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断表示の一方向。 -/
theorem dividedPowerPrimeTruncatedEval_surjective (hp : (p : A) = 0) :
    Function.Surjective (dividedPowerPrimeTruncatedEval (A := A) p hp) := by
  have hle : S ≤ (dividedPowerPrimeTruncatedEval (A := A) p hp).range := by
    apply Algebra.adjoin_le
    rintro _ ⟨n, rfl⟩
    exact ⟨Ideal.Quotient.mk _ (MvPolynomial.X n), dividedPowerPrimeTruncatedEval_X p hp n⟩
  rw [dividedPowerPrime_adjoin_eq_top p hp] at hle
  intro x
  exact hle (by trivial)

omit [Fact p.Prime] in
/-- 概要：切断多項式表示の関係イデアルは全変数の p 乗で生成される。
方針：モニック冪関係の右辺を零にした定義を展開する。
規約：この表示の等式には標数や素数性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の具体的な gᵢᵖ=0 の商表示。 -/
theorem dividedPowerPrimeTruncated_relationIdeal :
    monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0) =
      Ideal.span (Set.range fun n : ℕ => (MvPolynomial.X n : MvPolynomial ℕ A) ^ p) := by
  simp [monicPowerFamilyRelationIdeal]

omit [Fact p.Prime] in
/-- 概要：切断多項式商からの係数代数射は全変数上の値で一意に決まる。
方針：商と多項式代数の二つの射の外延性を使う。
規約：終域に標数や非零性を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の具体的表示の互換射。 -/
theorem dividedPowerPrimeTruncatedHom_ext {B : Type u} [CommRing B] [Algebra A B]
    (f g : DividedPowerPrimeTruncatedAlgebra (A := A) p →ₐ[A] B)
    (h : ∀ n : ℕ, f (Ideal.Quotient.mk _ (MvPolynomial.X n)) =
      g (Ideal.Quotient.mk _ (MvPolynomial.X n))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro n
  exact h n

end SerrePositivity.BhattScholze.Andre

end DividedPowerPrimeGenerators

/-! ## 有限切断多項式表示の分冪評価の単射性

## 概要

有限個の変数の p 乗を零とした多項式商を有限テンソル段と同定し、
標準分冪評価の単射性を証明する。BS 著者版 Remark 7.15(1)（著者版 p.62）。

## 方針

両者の変数による普遍性から互いに逆な射を作り、テンソル段の単射評価を移す。

## 規約

表示の同型には標数は不要。分冪評価には p の素数性と係数環内で p=0 を使う。

## 使われ方

可算切断表示の単射性を多項式の有限変数支持により得るために使う。
-/

@[expose] public noncomputable section DividedPowerPrimeFinitePresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p n : ℕ)
local notation "J" => monicPowerFamilyRelationIdeal p (Fin n) A (fun _ => 0)

/-- 概要：n 個の変数の p 乗を零にした通常多項式商。
方針：既存のモニック冪関係イデアルの右辺を零にする。
規約：p=0 と零係数環も定義に含める。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の有限切断表示。 -/
abbrev DividedPowerPrimeFiniteAlgebra := MvPolynomial (Fin n) A ⧸ J

/-- 概要：有限切断多項式商から有限テンソル段への標準射。
方針：テンソル段の各変数の p 乗消滅を使い評価を商へ降ろす。
規約：係数環作用を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の表示同型の順射。 -/
def dividedPowerPrimeFiniteToTensor :
    DividedPowerPrimeFiniteAlgebra (A := A) p n →ₐ[A]
      dividedPowerPrimeTensorStage (A := A) p n := by
  let g : MvPolynomial (Fin n) A →ₐ[A] dividedPowerPrimeTensorStage (A := A) p n :=
    MvPolynomial.aeval (dividedPowerPrimeTensorStageRoot (A := A) p n)
  apply Ideal.Quotient.liftₐ _ g
  have hker : J ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g (MvPolynomial.X i ^ p - MvPolynomial.C (0 : A)) = 0
    simp [g, dividedPowerPrimeTensorStageRoot_pow]
  exact fun _ hx => hker hx

/-- 概要：有限切断表示の順射は変数を同じ番号のテンソル変数へ送る。
方針：商からの多項式評価の公式を使う。
規約：変数番号を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の逆写像の確認。 -/
theorem dividedPowerPrimeFiniteToTensor_X (i : Fin n) :
    dividedPowerPrimeFiniteToTensor (A := A) p n (Ideal.Quotient.mk J (MvPolynomial.X i)) =
      dividedPowerPrimeTensorStageRoot (A := A) p n i := by
  simp [dividedPowerPrimeFiniteToTensor]

/-- 概要：有限テンソル段から有限切断多項式商への標準射。
方針：商の変数の p 乗消滅を有限テンソル段の普遍射へ渡す。
規約：標数仮定を使わない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の表示同型の逆射。 -/
def dividedPowerPrimeTensorToFinite : dividedPowerPrimeTensorStage (A := A) p n →ₐ[A]
    DividedPowerPrimeFiniteAlgebra (A := A) p n :=
  dividedPowerPrimeTensorStageLift (A := A) p n (fun i => Ideal.Quotient.mk J (MvPolynomial.X i))
    (fun i => by
      simpa only [map_zero] using
        (monicPowerFamilyQuotient_root_pow p (Fin n) A (fun _ => 0) i))

/-- 概要：有限切断表示からテンソル段へ移して戻すと元に戻る。
方針：商と多項式の射の外延性を使い、各変数で合成を確認する。
規約：係数環を固定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の表示の独立性。 -/
theorem dividedPowerPrimeTensorToFinite_comp_toTensor :
    (dividedPowerPrimeTensorToFinite (A := A) p n).comp
      (dividedPowerPrimeFiniteToTensor p n) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change dividedPowerPrimeTensorToFinite p n
    (dividedPowerPrimeFiniteToTensor p n (Ideal.Quotient.mk J (MvPolynomial.X i))) = _
  rw [dividedPowerPrimeFiniteToTensor_X]
  exact dividedPowerPrimeTensorStageLift_root (A := A) p n _ _ i

/-- 概要：テンソル段から有限切断表示へ移して戻しても元に戻る。
方針：テンソル段の変数上の外延性と普遍射の値を使う。
規約：係数環に非零性を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の表示同型の検証。 -/
theorem dividedPowerPrimeFiniteToTensor_comp_toFinite :
    (dividedPowerPrimeFiniteToTensor (A := A) p n).comp
      (dividedPowerPrimeTensorToFinite p n) = AlgHom.id A _ := by
  apply dividedPowerPrimeTensorStageHom_ext
  intro i
  change dividedPowerPrimeFiniteToTensor p n
    (dividedPowerPrimeTensorToFinite p n (dividedPowerPrimeTensorStageRoot p n i)) = _
  rw [show dividedPowerPrimeTensorToFinite p n (dividedPowerPrimeTensorStageRoot p n i) =
      Ideal.Quotient.mk J (MvPolynomial.X i) from
        dividedPowerPrimeTensorStageLift_root (A := A) p n _ _ i]
  exact dividedPowerPrimeFiniteToTensor_X p n i

/-- 概要：有限切断多項式商は有限反復テンソル段と係数代数として同型。
方針：互いに逆であることを確認した具体的な二射を束ねる。
規約：素数性と標数はこの同型には不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断多項式の独立性の移送。 -/
def dividedPowerPrimeFiniteTensorEquiv : DividedPowerPrimeFiniteAlgebra (A := A) p n ≃ₐ[A]
    dividedPowerPrimeTensorStage (A := A) p n :=
  AlgEquiv.ofAlgHom (dividedPowerPrimeFiniteToTensor p n) (dividedPowerPrimeTensorToFinite p n)
    (dividedPowerPrimeFiniteToTensor_comp_toFinite p n)
    (dividedPowerPrimeTensorToFinite_comp_toTensor p n)

/-- 概要：有限切断多項式商の標準分冪評価射。
方針：表示同型を有限テンソル段の標準評価と合成する。
規約：p は素数で係数環内で零。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の可算表示の有限支持への制限。 -/
def dividedPowerPrimeFiniteEval [Fact p.Prime] (hp : (p : A) = 0) :
    DividedPowerPrimeFiniteAlgebra (A := A) p n →ₐ[A] DividedPowerAlgebra A A :=
  (dividedPowerPrimeTensorStageEval p hp n).comp (dividedPowerPrimeFiniteToTensor p n)

/-- 概要：有限切断評価は変数 i を γₚⁱ へ送る。
方針：表示射の変数公式とテンソル段の分冪評価を使う。
規約：変数の番号は Fin n の自然数値を使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の可算評価との互換性。 -/
theorem dividedPowerPrimeFiniteEval_X [Fact p.Prime] (hp : (p : A) = 0) (i : Fin n) :
    dividedPowerPrimeFiniteEval p n hp (Ideal.Quotient.mk J (MvPolynomial.X i)) =
      DividedPowerAlgebra.dp A (p ^ (i : ℕ)) (1 : A) := by
  change dividedPowerPrimeTensorStageEval p hp n
    (dividedPowerPrimeFiniteToTensor p n (Ideal.Quotient.mk J (MvPolynomial.X i))) = _
  rw [dividedPowerPrimeFiniteToTensor_X, dividedPowerPrimeTensorStageEval_root]

/-- 概要：有限切断多項式商から一元分冪代数への標準評価は単射。
方針：表示同型と有限テンソル段の単射評価を合成する。
規約：追加の平坦性や係数環の非零性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の可算表示の単射性の有限段。 -/
theorem dividedPowerPrimeFiniteEval_injective [Fact p.Prime] (hp : (p : A) = 0) :
    Function.Injective (dividedPowerPrimeFiniteEval (A := A) p n hp) :=
  (dividedPowerPrimeTensorStageEval_injective p hp n).comp
    (dividedPowerPrimeFiniteTensorEquiv (A := A) p n).injective

end SerrePositivity.BhattScholze.Andre

end DividedPowerPrimeFinitePresentation

/-! ## 一元分冪代数の可算切断多項式表示

## 概要

p が零となる可換係数環上の一元分冪代数は、変数 i を γₚⁱ に送る射により
可算切断多項式商 A[g₀,g₁,…]/(gᵢᵖ) と同型である。
BS 著者版 Remark 7.15(1)（著者版 p.62）の明示的な表示の自由分冪代数側。

## 方針

任意の多項式は有限個の初期変数から来る。有限切断評価の単射性と、
既に証明した可算評価の全射性を組み合わせる。

## 規約

p は素数で A 内で零。γ₁=f の商や実 pd 包の普遍性は別途必要である。

## 使われ方

γ₁=f を課した商を係数商と残りの切断変数に分離する計算へ進む。
-/

@[expose] public noncomputable section DividedPowerPrimePresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ)
local notation "Q" => DividedPowerPrimeTruncatedAlgebra (A := A) p

/-- 概要：有限初期変数の切断商を可算切断商へ送る標準射。
方針：有限変数を自然数番号へ名前変更する多項式射を関係式商へ降ろす。
規約：標数や素数性はこの射には不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の有限支持からの比較。 -/
def dividedPowerPrimeFiniteToCountable (n : ℕ) :
    DividedPowerPrimeFiniteAlgebra (A := A) p n →ₐ[A] Q := by
  let g : MvPolynomial (Fin n) A →ₐ[A] Q :=
    (Ideal.Quotient.mkₐ A _).comp (MvPolynomial.rename (fun i : Fin n => (i : ℕ)))
  apply Ideal.Quotient.liftₐ _ g
  have hker : monicPowerFamilyRelationIdeal p (Fin n) A (fun _ => 0) ≤
      RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g (MvPolynomial.X i ^ p - MvPolynomial.C (0 : A)) = 0
    simp only [g, map_pow, AlgHom.comp_apply, MvPolynomial.rename_X, map_zero, sub_zero]
    change (Ideal.Quotient.mk (monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0))
      (MvPolynomial.X i.val)) ^ p = 0
    simpa only [map_zero] using monicPowerFamilyQuotient_root_pow p ℕ A (fun _ => 0) i.val
  exact fun _ hx => hker hx

/-- 概要：有限から可算への標準射は商の多項式を変数名変更で送る。
方針：商からの普遍射の評価を展開する。
規約：添字は Fin n の自然数値を使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の有限支持への制限。 -/
theorem dividedPowerPrimeFiniteToCountable_mk (n : ℕ) (F : MvPolynomial (Fin n) A) :
    dividedPowerPrimeFiniteToCountable (A := A) p n (Ideal.Quotient.mk _ F) =
      Ideal.Quotient.mk _ (MvPolynomial.rename (fun i : Fin n => (i : ℕ)) F) := rfl

/-- 概要：可算切断商の任意の元はある有限初期変数商から来る。
方針：代表多項式の有限変数集合の上限より大きい段を選び、名前変更で引き戻す。
規約：係数環の非零性や標数を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の可算評価の単射性を有限段へ帰着する。 -/
theorem dividedPowerPrimeCountable_exists_finite (x : Q) :
    ∃ (n : ℕ) (y : DividedPowerPrimeFiniteAlgebra (A := A) p n),
      dividedPowerPrimeFiniteToCountable p n y = x := by
  classical
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  let n := F.vars.sup id + 1
  have hvars : (F.vars : Set ℕ) ⊆ Set.range (fun i : Fin n => (i : ℕ)) := by
    intro i hi
    refine ⟨⟨i, ?_⟩, rfl⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  obtain ⟨G, hG⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range F
    (fun i : Fin n => (i : ℕ)) Fin.val_injective hvars
  refine ⟨n, Ideal.Quotient.mk _ G, ?_⟩
  rw [dividedPowerPrimeFiniteToCountable_mk, hG]

/-- 概要：有限段の評価は可算段への標準射と可算評価の合成に一致する。
方針：商と多項式の外延性で各変数の評価 γₚⁱ を比較する。
規約：p は素数で係数環内で零。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の単射性の移送。 -/
theorem dividedPowerPrimeTruncatedEval_comp_finite [Fact p.Prime]
    (hp : (p : A) = 0) (n : ℕ) :
    (dividedPowerPrimeTruncatedEval (A := A) p hp).comp
      (dividedPowerPrimeFiniteToCountable p n) = dividedPowerPrimeFiniteEval p n hp := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change dividedPowerPrimeTruncatedEval p hp
    (dividedPowerPrimeFiniteToCountable p n (Ideal.Quotient.mk _ (MvPolynomial.X i))) = _
  rw [dividedPowerPrimeFiniteToCountable_mk, MvPolynomial.rename_X]
  exact (dividedPowerPrimeTruncatedEval_X p hp i.val).trans
    (dividedPowerPrimeFiniteEval_X p n hp i).symm

/-- 概要：可算切断多項式商から一元分冪代数への標準評価は単射。
方針：核の任意の元を有限段から持ち上げ、有限評価の単射性で零とする。
規約：係数環の非零性や追加の平坦性を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示的な自由切断表示。 -/
theorem dividedPowerPrimeTruncatedEval_injective [Fact p.Prime] (hp : (p : A) = 0) :
    Function.Injective (dividedPowerPrimeTruncatedEval (A := A) p hp) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨n, y, rfl⟩ := dividedPowerPrimeCountable_exists_finite p x
  have hy : dividedPowerPrimeFiniteEval p n hp y = 0 := by
    rw [← dividedPowerPrimeTruncatedEval_comp_finite]
    exact hx
  have hy0 : y = 0 := (dividedPowerPrimeFiniteEval_injective p n hp)
    (hy.trans (map_zero _).symm)
  rw [hy0, map_zero]

/-- 概要：可算切断多項式商は標準評価によって一元分冪代数に同型。
方針：有限支持から得た単射性と素数冪分冪の生成による全射性を束ねる。
規約：変数 i は γₚⁱ に対応し、原典の γ₁=f の商はまだ課さない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 表示計算の基礎同型。 -/
def dividedPowerPrimeTruncatedEquiv [Fact p.Prime] (hp : (p : A) = 0) :
    Q ≃ₐ[A] DividedPowerAlgebra A A :=
  AlgEquiv.ofBijective (dividedPowerPrimeTruncatedEval p hp)
    ⟨dividedPowerPrimeTruncatedEval_injective p hp,
      dividedPowerPrimeTruncatedEval_surjective p hp⟩


/-- 概要：切断表示の代数同型は変数 i を γₚⁱ に送る。
方針：同型の順射が標準評価であることと既存の変数公式を使う。
規約：最初の変数 i=0 は一次分冪 γ₁ に対応する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の γ₁=f の商の比較。 -/
theorem dividedPowerPrimeTruncatedEquiv_X [Fact p.Prime] (hp : (p : A) = 0) (i : ℕ) :
    dividedPowerPrimeTruncatedEquiv p hp (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      DividedPowerAlgebra.dp A (p ^ i) (1 : A) :=
  dividedPowerPrimeTruncatedEval_X p hp i

end SerrePositivity.BhattScholze.Andre

end DividedPowerPrimePresentation

/-! ## 可算切断表示の普遍射と素数冪生成元の外延性

## 概要

可算切断商からの射を p 乗が零となる元族から構成し、
一元分冪代数と一次関係商からの射を素数冪分冪の値で比較する。
BS 著者版 Remark 7.15(1)（著者版 p.62）の γ₁=f の商を計算する準備。

## 方針

多項式評価を商に降ろし、既に構成した可算切断表示の全射性を使う。

## 規約

普遍射自体は任意の自然数 p に対して定義する。分冪側の外延性には
p が素数で係数環内で零であることを使う。

## 使われ方

一次関係商と係数 p 乗商上の切断多項式商の間に互いに逆な射を構成する。
-/

@[expose] public noncomputable section DividedPowerPrimeUniversal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ)
variable {B : Type u} [CommRing B] [Algebra A B]

/-- 概要：p 乗が零となる元族への指定値から可算切断商の係数代数射を作る。
方針：多項式評価が全ての p 乗関係を消すことを使う。
規約：素数性や標数は前提にしない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の切断商の普遍性。 -/
def dividedPowerPrimeTruncatedLift (b : ℕ → B) (hb : ∀ i, b i ^ p = 0) :
    DividedPowerPrimeTruncatedAlgebra (A := A) p →ₐ[A] B := by
  let g : MvPolynomial ℕ A →ₐ[A] B := MvPolynomial.aeval b
  apply Ideal.Quotient.liftₐ _ g
  have hker : monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0) ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g (MvPolynomial.X i ^ p - MvPolynomial.C (0 : A)) = 0
    simp [g, hb]
  exact fun _ hx => hker hx

/-- 概要：可算切断商の普遍射は変数を指定した元へ送る。
方針：商と多項式評価の公式を使う。
規約：変数番号を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の二つの表示の比較。 -/
theorem dividedPowerPrimeTruncatedLift_X (b : ℕ → B) (hb : ∀ i, b i ^ p = 0) (i : ℕ) :
    dividedPowerPrimeTruncatedLift (A := A) p b hb
      (Ideal.Quotient.mk _ (MvPolynomial.X i)) = b i := by
  simp [dividedPowerPrimeTruncatedLift]

/-- 概要：一元分冪代数からの射は全素数冪分冪上の値で一意に決まる。
方針：可算切断評価の全射性と、切断変数上の外延性を使う。
規約：p は素数で係数環内で零。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の一次関係商の射の照合。 -/
theorem dividedPowerPrimeHom_ext [Fact p.Prime] (hp : (p : A) = 0)
    (f g : DividedPowerAlgebra A A →ₐ[A] B)
    (h : ∀ i, f (DividedPowerAlgebra.dp A (p ^ i) (1 : A)) =
      g (DividedPowerAlgebra.dp A (p ^ i) (1 : A))) : f = g := by
  have hc : f.comp (dividedPowerPrimeTruncatedEval p hp) =
      g.comp (dividedPowerPrimeTruncatedEval p hp) := by
    apply dividedPowerPrimeTruncatedHom_ext
    intro i
    simpa only [AlgHom.comp_apply, dividedPowerPrimeTruncatedEval_X] using h i
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := dividedPowerPrimeTruncatedEval_surjective p hp x
  exact DFunLike.congr_fun hc y

/-- 概要：一次関係商からの射は全素数冪分冪の標準像上の値で一意に決まる。
方針：商の射を自由分冪代数へ引き戻し、素数冪生成元で比較する。
規約：入力 y の正則性はこの外延性には不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の表示同型の逆合成の確認。 -/
theorem principalDPPrimeHom_ext [Fact p.Prime] (hp : (p : A) = 0) (y : A)
    (f g : PrincipalDPPresentation A y →ₐ[A] B)
    (h : ∀ i, f (principalDPGenerator y (p ^ i)) =
      g (principalDPGenerator y (p ^ i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply dividedPowerPrimeHom_ext p hp
  exact h

end SerrePositivity.BhattScholze.Andre

end DividedPowerPrimeUniversal

/-! ## André：分冪表示環の実 p 乗商上の自由性

## 概要

標数 p の任意の環 B と元 y について、具体的な分冪表示環は B/(y^p) 上自由である。
BS 著者版 Remark 7.15(1)（p.62）の自由性の計算を既存の一元分冪基底から得る。

## 方針

切断多項式環上の自由基底の基底変更を、実 y 評価商と整合する係数射に沿って移す。
最後に分冪表示環と評価テンソルの代数同型で自由性を戻す。

## 規約

対象は `PrincipalDPPresentation` であり、実 prismatic envelope との同型は含まない。
本結果は y の非零因子性を必要としない。原典の prismatic cover の証明とは別の通常代数計算。

## 使われ方

モニック f の商 B/(f^p) の自由性と合成し、元の係数環上の分冪表示環の自由性を得る。
-/

@[expose] public noncomputable section PrincipalDPFree

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra

/-- 概要：評価した分冪添加環は元 y の実 p 乗商上自由。
方針：評価商の同定を経由して、既存の切断多項式上の基底を移す。
規約：係数射は `rankOneDPEvaluatedQuotientAlgebra` の指定射に固定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の分冪表示環の自由性。 -/
theorem evaluatedDP_quotient_free
    {B : Type u} [CommRing B] (p : ℕ) (hprime : p.Prime) (hp : (p : B) = 0) (y : B) :
    letI := rankOneDPEvaluatedQuotientAlgebra (A := B) hprime.pos hp y
    Module.Free (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope B B y) := by
  let : Algebra (Polynomial B) B := rankOneDPEvaluationAlgebra (A := B) y
  let Q := B ⧸ Ideal.span {y ^ p}
  let Q' := B ⧸ Ideal.span {(algebraMap (Polynomial B) B Polynomial.X) ^ p}
  let T := RankOneDPEvaluatedEnvelope B B y
  let eQ : Q ≃+* Q' := Ideal.quotEquivOfEq (rankOneDPEvaluatedRelationIdeal (A := B) p y)
  let : Algebra Q Q' := eQ.toRingHom.toAlgebra
  let : Algebra Q' T := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : Algebra Q T := rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
  let : IsScalarTower Q Q' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e : Q ≃ₐ[Q] Q' := { __ := eQ, commutes' := fun _ => rfl }
  let : Module.Free Q Q' :=
    Module.Free.of_basis ((Module.Basis.singleton Unit Q).map e.toLinearEquiv)
  let : Module.Free Q' T := rankOneDPQuotientToEnvelope_moduleFree hprime hp
  exact Module.Free.trans (R := Q) (S := Q') (M := T)

/-- 概要：具体的分冪表示環は元の実 p 乗商上自由。
方針：実商上の代数同型で評価した分冪添加環の自由性を戻す。
規約：零環と零因子 y を許す。実 pd 包との同定は別工程。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック関係の自由性。 -/
theorem principalDPPresentation_quotient_free
    {B : Type u} [CommRing B] (p : ℕ) (hprime : p.Prime) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hprime.pos hp y
    Module.Free (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hprime.pos hp y
  let := rankOneDPEvaluatedQuotientAlgebra (A := B) hprime.pos hp y
  let := evaluatedDP_quotient_free p hprime hp y
  exact Module.Free.of_equiv (principalDPQuotientTensorAlgEquiv hprime.pos hp y).symm.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end PrincipalDPFree

/-! ## 正次数商で正則な元による実分冪構造の降下

## 概要

環 D の分冪イデアル J に対し、D/J で正則な元 a による商へ実分冪構造が降りる。
BS 著者版 Remark 7.15(1)（著者版 p.62）の係数 R/ϖ への比較のための一般補題。

## 方針

ab が J に入れば商での a の正則性により b も J に入る。
γₙ(ab)=aⁿγₙ(b) から (a) と J の交わりの分冪安定性を得て、商 API を適用する。

## 規約

a の環 D 自身での正則性は要求しない。分冪イデアルによる商での正則性を明示する。

## 使われ方

正次数商の係数環上の自由性から係数元の正則性を供給し、実分冪構造を係数商へ移す。
-/

@[expose] public noncomputable section DividedPowerRegularQuotient

namespace SerrePositivity.BhattScholze.Andre
variable {D : Type u} [CommRing D] {J : Ideal D} (H : DividedPowers J) (a : D)
variable (ha : IsSMulRegular (D ⧸ J) (Ideal.Quotient.mk J a))
include ha

/-- 概要：D/J で正則な a に対し (a) と J の交わりは分冪で保たれる。
方針：ab が J に属すれば b も属し、正次数分冪は a の倍数になる。
規約：全ての正次数を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数元による分冪降下の入力。 -/
theorem dividedPower_regular_span_inf_isSubDPIdeal :
    H.IsSubDPIdeal (Ideal.span {a} ⊓ J) := by
  refine ⟨inf_le_right, ?_⟩
  intro n hn x hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx.1
  have hb : Ideal.Quotient.mk J b = 0 := by
    apply ha
    change Ideal.Quotient.mk J a * Ideal.Quotient.mk J b = Ideal.Quotient.mk J a * 0
    rw [mul_zero, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx.2
  have hbJ : b ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hb
  refine ⟨?_, H.dpow_mem hn hx.2⟩
  rw [H.dpow_mul hbJ]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_left (dvd_pow_self a hn) _)

/-- 概要：D/J で正則な元 a による商の像イデアルに実分冪構造を与える。
方針：(a) と J の交わりの分冪安定性を商構成へ渡す。
規約：対象は J の実商射による像である。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数商上の実 pd 構造。 -/
def dividedPowersQuotientOfRegular :
    DividedPowers (J.map (Ideal.Quotient.mk (Ideal.span {a}))) :=
  DividedPowers.Quotient.dividedPowers H (dividedPower_regular_span_inf_isSubDPIdeal H a ha)

/-- 概要：降下した分冪作用は元の分冪値の商像に一致する。
方針：実商の分冪作用の標準評価公式を使う。
規約：元を元の分冪イデアル J 内に取る。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の生成元と普遍性の比較。 -/
theorem dividedPowersQuotientOfRegular_apply (n : ℕ) {x : D} (hx : x ∈ J) :
    (dividedPowersQuotientOfRegular H a ha).dpow n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (H.dpow n x) :=
  DividedPowers.Quotient.dpow_apply H (dividedPower_regular_span_inf_isSubDPIdeal H a ha) hx

/-- 概要：正則係数元による標準商射は分冪射。
方針：商構成の分冪射の互換性を使う。
規約：元のイデアル J とその実像を比較する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の係数変更。 -/
theorem dividedPowersQuotientOfRegular_isDPMorphism :
    H.IsDPMorphism (dividedPowersQuotientOfRegular H a ha) (Ideal.Quotient.mk (Ideal.span {a})) :=
  DividedPowers.Quotient.isDPMorphism H (dividedPower_regular_span_inf_isSubDPIdeal H a ha)

end SerrePositivity.BhattScholze.Andre

end DividedPowerRegularQuotient

/-! ## 射影的な正次数商を使う任意係数元による分冪降下

## 概要

R 代数 D の分冪イデアル J に対し、D/J が R 上射影的なら、任意の係数元 a による
商へ分冪構造が降りる。BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック入力の係数還元。

## 方針

D→D/J の R 線形切断を取り、a b∈J を a c（c∈J）と書き直す。
分冪の積公式から係数主イデアルとの交わりの安定性を証明する。
原典とは異なる射影性による切断を使う証明である。

## 規約

係数元の正則性は仮定しない。分冪構造は実際の像イデアルに与える。

## 使われ方

モニック入力による正次数商の自由性から射影性を得て、prism 商の p 正則性を使わずに降下する。
-/

@[expose] public noncomputable section DividedPowerProjectiveCoefficientQuotient

namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} {D : Type v} [CommRing R] [CommRing D] [Algebra R D]
variable {J : Ideal D} [Module.Projective R (D ⧸ J)]

/-- 概要：係数倍が J に入れば同じ係数倍を J 内の元で表せる。
方針：射影的な商への線形切断を b から差し引き、係数倍が変わらないことを示す。
規約：係数元 a の零因子を許す。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数主イデアルと分冪イデアルの交わり。 -/
theorem exists_coefficient_mul_representative_of_projective_quotient
    (a : R) (b : D) (hb : algebraMap R D a * b ∈ J) :
    ∃ c ∈ J, algebraMap R D a * c = algebraMap R D a * b := by
  let q : D →ₗ[R] D ⧸ J := (Ideal.Quotient.mkₐ R J).toLinearMap
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective R J))
  have hs' (y : D ⧸ J) : q (s y) = y := congrArg (fun F : (D ⧸ J) →ₗ[R] D ⧸ J => F y) hs
  let c := b - s (q b)
  have hc : q c = 0 := by
    dsimp only [c]
    rw [map_sub, hs', sub_self]
  have hcJ : c ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hc
  have hqb : a • q b = 0 := by
    rw [← map_smul q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [Algebra.smul_def] using hb)
  have hsb : a • s (q b) = 0 := by
    rw [← map_smul s, hqb, map_zero]
  refine ⟨c, hcJ, ?_⟩
  rw [← Algebra.smul_def, ← Algebra.smul_def]
  change a • (b - s (q b)) = a • b
  rw [smul_sub, hsb, sub_zero]

variable (H : DividedPowers J) (a : R)

/-- 概要：任意の係数主イデアルと分冪イデアルの交わりは分冪で安定。
方針：係数倍を J 内の元の係数倍に書き直し、正次数分冪の積公式を使う。
規約：D/J の R 上の射影性のみを要求し、係数元の正則性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数商への実分冪降下。 -/
theorem dividedPower_coefficient_span_inf_isSubDPIdeal_of_projective :
    H.IsSubDPIdeal (Ideal.span {algebraMap R D a} ⊓ J) := by
  refine ⟨inf_le_right, ?_⟩
  intro n hn x hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx.1
  obtain ⟨c, hcJ, hc⟩ :=
    exists_coefficient_mul_representative_of_projective_quotient a b hx.2
  refine ⟨?_, H.dpow_mem hn hx.2⟩
  rw [← hc, H.dpow_mul hcJ]
  exact Ideal.mem_span_singleton.mpr
    (dvd_mul_of_dvd_left (dvd_pow_self (algebraMap R D a) hn) _)

/-- 概要：射影的な正次数商を持つ実分冪構造は任意係数元の商へ降りる。
方針：係数主イデアルとの交わりの分冪安定性を通常商の構成へ渡す。
規約：元の J の実商射による像イデアルを使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正則性を要求しない係数還元。 -/
def dividedPowersQuotientOfProjectiveCoefficient :
    DividedPowers (J.map (Ideal.Quotient.mk (Ideal.span {algebraMap R D a}))) :=
  DividedPowers.Quotient.dividedPowers H
    (dividedPower_coefficient_span_inf_isSubDPIdeal_of_projective H a)

/-- 概要：係数還元後の分冪値は還元前の実分冪値の商像。
方針：分冪商の標準評価公式を使う。
規約：全次数 n と元の J の任意の元を含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の入力元の分冪値の追跡。 -/
theorem dividedPowersQuotientOfProjectiveCoefficient_apply
    (n : ℕ) {x : D} (hx : x ∈ J) :
    (dividedPowersQuotientOfProjectiveCoefficient H a).dpow n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (H.dpow n x) :=
  DividedPowers.Quotient.dpow_apply H
    (dividedPower_coefficient_span_inf_isSubDPIdeal_of_projective H a) hx

/-- 概要：射影的な正次数商による任意係数還元の商射は分冪射。
方針：構成済みの分冪商の射の互換性を使う。
規約：同じ係数元の主イデアルと同じ像イデアルを比較する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の還元後の pd 普遍性への接続。 -/
theorem dividedPowersQuotientOfProjectiveCoefficient_isDPMorphism :
    H.IsDPMorphism (dividedPowersQuotientOfProjectiveCoefficient H a)
      (Ideal.Quotient.mk (Ideal.span {algebraMap R D a})) :=
  DividedPowers.Quotient.isDPMorphism H
    (dividedPower_coefficient_span_inf_isSubDPIdeal_of_projective H a)

end SerrePositivity.BhattScholze.Andre

end DividedPowerProjectiveCoefficientQuotient
