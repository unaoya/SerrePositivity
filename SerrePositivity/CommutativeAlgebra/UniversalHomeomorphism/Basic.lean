module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# 可換環の射の普遍同相

## 概要
整性と Spec の全射性、単射性、剰余体拡大の純非分離性で普遍同相を表す。

## 方針
標数 p では核が nil であり、各元の適当な p 冪が像に入ることで判定する。

## 規約
核の条件は `RingHom.ker f ≤ nilradical A`。冪零指数は元ごとに取る。

## 使われ方
有限エタール層別の各層の後半の射を記述する（BS Lemma 10.12）。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 概要：G-A8-4：環の射が普遍同相：整・Spec で全射・radicial（普遍単射：剰余体の拡大が純非分離で Spec で単射）。
方針：定義。
規約：—
使われ方：Lemma 10.12 (2)。 -/
structure IsUniversalHomeomorphism {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop where
  isIntegral : f.IsIntegral
  surjective_spec : Function.Surjective (PrimeSpectrum.comap f)
  radicial : Function.Injective (PrimeSpectrum.comap f) ∧
    ∀ Q : PrimeSpectrum B,
      let P := (PrimeSpectrum.comap f Q).asIdeal
      letI := (Ideal.ResidueField.map P Q.asIdeal f rfl).toAlgebra
      IsPurelyInseparable P.ResidueField Q.asIdeal.ResidueField

/-- 概要：普遍同相は底変換・合成で安定、nil イデアルによる商は普遍同相。 -/
theorem isUniversalHomeomorphism_baseChange {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) (hf : IsUniversalHomeomorphism f) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A C := g.toAlgebra
    IsUniversalHomeomorphism (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom := by
  sorry -- 整性は底変換で保たれる。各点の幾何学的ファイバーが非空で一点であることも保たれる

theorem isUniversalHomeomorphism_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : IsUniversalHomeomorphism f)
    (hg : IsUniversalHomeomorphism g) : IsUniversalHomeomorphism (g.comp f) := by
  sorry -- 整性と剰余体の純非分離性の推移性、および Spec の全単射の合成

theorem isUniversalHomeomorphism_of_nil_kernel {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical A) :
    IsUniversalHomeomorphism f := by
  sorry -- nil な核は全ての素イデアルに含まれ、商写像は Spec で全単射かつ各剰余体で同型

/-- 概要：標数 p の判定：F_p 代数の射が普遍同相 ⇔ 核の各元が冪零で、各 b の或る p^n 乗が像にある。 -/
theorem isUniversalHomeomorphism_iff_charP {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0) (f : A →+* B) :
    IsUniversalHomeomorphism f ↔
      RingHom.ker f ≤ nilradical A ∧ ∀ b : B, ∃ n : ℕ, b ^ (p ^ n) ∈ f.range := by
  sorry -- 普遍同相の標数 p の判定。核は Spec の全射性から nil、p 冪の指数は元ごとに取る

/-- 概要：G-A8-5：完全 F_p 環 A から被約環 B への普遍同相は同型。
方針：b^{p^n} = f(a)、a = σ^{p^n}、(b − f σ)^{p^n} = 0、B 被約 ⇒ b = f σ；核は nil で A 被約 ⇒ 零。
規約：`PerfectRing A p`。
使われ方：Thm 10.11 の n = 1 と 5。 -/
theorem isUniversalHomeomorphism_bijective_of_perfect_reduced
    {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0) [PerfectRing A p] [IsReduced B]
    (f : A →+* B) (hf : IsUniversalHomeomorphism f) : Function.Bijective f := by
  sorry -- A は被約なので nil な核は零。b^(p^n) = f(a) で a の p^n 乗根 σ を取り、B の被約性で b = f(σ)

/-- 概要：純非分離な体の拡大は普遍同相。
方針：両側の Spec の唯一の点で剰余体の射を同定する。 -/
theorem isUniversalHomeomorphism_of_isPurelyInseparable (K L : Type u) [Field K] [Field L]
    [Algebra K L] [IsPurelyInseparable K L] : IsUniversalHomeomorphism (algebraMap K L) := by
  sorry -- 純非分離拡大は整、双方の Spec は一点でその剰余体の射が K→L

end SerrePositivity.CommutativeAlgebra
