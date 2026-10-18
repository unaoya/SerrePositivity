module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# 有理降下の持ち上げから正の整数倍の持ち上げへ

## 概要
有理テンソル積で持ち上がるアーベル群の元は、正の整数倍が元の群の射で持ち上がる。

## 方針
有理テンソル積への標準射の局所化表示で分母を払い、等式の検出でねじれを消す。

## 規約
元の群のねじれなし性や有限生成性を要求しない。有理降下そのものは証明しない。

## 使われ方
論文 定理 3.1、(3.2) の有理全射性から theorem_3_1_K0 と §4 の整数形への接続。
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace SerrePositivity.KST.Descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]

/-- 概要：非零整数倍の持ち上げを正の自然数倍へ直す（定理 3.1 の整数形）。
方針：整数の符号に応じて持ち上げ元の符号を変える。
規約：像の群のねじれなし性は不要。
使われ方：分母とねじれを消した後の正値性。 -/
theorem positive_multiple_of_nonzero_integer_multiple (f : A →+ B) (b : B)
    (m : ℤ) (hm : m ≠ 0) (a : A) (h : m • b = f a) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ n • b = f x := by
  cases m with
  | ofNat n =>
    refine ⟨n, a, Nat.pos_of_ne_zero (fun hn ↦ hm (by simp [hn])), ?_⟩
    change (n : ℤ) • b = f a at h
    simpa only [natCast_zsmul] using h
  | negSucc n =>
    refine ⟨n + 1, -a, Nat.succ_pos n, ?_⟩
    simpa only [negSucc_zsmul, neg_neg, map_neg] using congrArg Neg.neg h

/-- 概要：群の射の標準の有理スカラー拡大（定理 3.1 の整数形への接続）。
方針：ℤ 上のテンソル積の写像を使う。
規約：テンソルの順は ℚ ⊗ A。スペクトルの有理化は定義しない。
使われ方：有理化後の指定写像の持ち上げを元の整数写像へ戻す。 -/
noncomputable def rationalScalarExtensionMap (f : A →+ B) :
    ℚ ⊗[ℤ] A →ₗ[ℤ] ℚ ⊗[ℤ] B :=
  TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) f.toIntLinearMap

/-- 概要：標準の有理拡大写像の単純テンソルでの値（定理 3.1）。
方針：テンソル積の写像の計算式を使う。
規約：任意の有理数を左係数とする。
使われ方：整数倍の持ち上げから有理持ち上げを構成する。 -/
@[simp] theorem rationalScalarExtensionMap_tmul (f : A →+ B) (q : ℚ) (a : A) :
    rationalScalarExtensionMap f (q ⊗ₜ[ℤ] a) = q ⊗ₜ[ℤ] f a := by
  rw [rationalScalarExtensionMap, TensorProduct.map_tmul]
  rfl

/-- 概要：標準の有理拡大写像は 1 ⊗ a を 1 ⊗ f(a) へ送る（定理 3.1）。
方針：テンソル積写像を単純テンソルで計算する。
規約：元の群の射そのものを使う。
使われ方：分母消去の自然性の等式。 -/
@[simp] theorem rationalScalarExtensionMap_unit (f : A →+ B) (a : A) :
    rationalScalarExtensionMap f (1 ⊗ₜ[ℤ] a) = 1 ⊗ₜ[ℤ] f a := by
  rw [rationalScalarExtensionMap, TensorProduct.map_tmul]
  rfl

/-- 概要：有理拡大で持ち上がる元は正の整数倍が元の群で持ち上がる（定理 3.1、(3.2)）。
方針：持ち上げ元の分母を払い、有理化で等しい二つの元の差のねじれをさらに消す。
規約：ねじれや分母を無視せず、両方を消してから正の自然数倍に直す。
使われ方：実際の有理降下比較と K0・T2 の自然な同定を得た後の整数版の帰結。 -/
theorem positive_multiple_of_rational_tensor_lift (f : A →+ B) (b : B)
    (t : ℚ ⊗[ℤ] A) (ht : rationalScalarExtensionMap f t = 1 ⊗ₜ[ℤ] b) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ n • b = f x := by
  let uA : A →ₗ[ℤ] ℚ ⊗[ℤ] A := TensorProduct.mk ℤ ℚ A 1
  let uB : B →ₗ[ℤ] ℚ ⊗[ℤ] B := TensorProduct.mk ℤ ℚ B 1
  have : IsLocalizedModule (nonZeroDivisors ℤ) uA :=
    inferInstanceAs (IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ A 1))
  have : IsLocalizedModule (nonZeroDivisors ℤ) uB :=
    inferInstanceAs (IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ B 1))
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) uA t
  change (s : ℤ) • t = uA a at hs
  have hunit : rationalScalarExtensionMap f (uA a) = uB (f a) :=
    rationalScalarExtensionMap_unit f a
  have heq : uB (f a) = uB ((s : ℤ) • b) := by
    calc
      _ = rationalScalarExtensionMap f (uA a) := hunit.symm
      _ = rationalScalarExtensionMap f ((s : ℤ) • t) :=
        congrArg (rationalScalarExtensionMap f) hs.symm
      _ = (s : ℤ) • uB b := by rw [map_smul, ht]; rfl
      _ = uB ((s : ℤ) • b) := (uB.map_smul (s : ℤ) b).symm
  obtain ⟨d, hd⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ) (f := uB) heq
  change (d : ℤ) • f a = (d : ℤ) • ((s : ℤ) • b) at hd
  have hm : (d : ℤ) * (s : ℤ) ≠ 0 := mul_ne_zero
    (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
    (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
  have hmul : ((d : ℤ) * (s : ℤ)) • b = f ((d : ℤ) • a) := by
    simpa only [mul_smul, map_zsmul] using hd.symm
  exact positive_multiple_of_nonzero_integer_multiple f b _ hm _ hmul

/-- 概要：A ⊗ ℚ の順の有理持ち上げからも正の整数倍を得る（定理 3.1、(3.2)）。
方針：テンソルの交換同型と指定写像の自然性で ℚ ⊗ A の順へ移す。
規約：元の群にねじれを許す。テンソルの順の変更を明示する。
使われ方：K0 の通常の有理化表記 a ⊗ 1 と整数形の接続。 -/
theorem positive_multiple_of_rational_tensor_lift_right (f : A →+ B) (b : B)
    (t : A ⊗[ℤ] ℚ)
    (ht : TensorProduct.map f.toIntLinearMap (LinearMap.id : ℚ →ₗ[ℤ] ℚ) t =
      b ⊗ₜ[ℤ] (1 : ℚ)) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ n • b = f x := by
  apply positive_multiple_of_rational_tensor_lift f b (TensorProduct.comm ℤ A ℚ t)
  have hc : rationalScalarExtensionMap f (TensorProduct.comm ℤ A ℚ t) =
      TensorProduct.comm ℤ B ℚ
        (TensorProduct.map f.toIntLinearMap (LinearMap.id : ℚ →ₗ[ℤ] ℚ) t) :=
    TensorProduct.map_comm (LinearMap.id : ℚ →ₗ[ℤ] ℚ) f.toIntLinearMap t
  exact hc.trans ((congrArg (TensorProduct.comm ℤ B ℚ) ht).trans (by simp))

/-- 概要：有理化での持ち上げと正の整数倍の持ち上げは同値（定理 3.1、(3.2)）。
方針：順方向は分母とねじれを消し、逆方向は指定整数の逆数をテンソルの左係数に取る。
規約：元の群の有限生成性・ねじれなし性は不要。
使われ方：K0 の整数形と実際の有理比較の対応を確認する。 -/
theorem rational_tensor_lift_iff_positive_multiple (f : A →+ B) (b : B) :
    (∃ t : ℚ ⊗[ℤ] A, rationalScalarExtensionMap f t = 1 ⊗ₜ[ℤ] b) ↔
      ∃ (n : ℕ) (x : A), 0 < n ∧ n • b = f x := by
  constructor
  · rintro ⟨t, ht⟩
    exact positive_multiple_of_rational_tensor_lift f b t ht
  · rintro ⟨n, x, hn, hx⟩
    have hne : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨(n : ℚ)⁻¹ ⊗ₜ[ℤ] x, ?_⟩
    rw [rationalScalarExtensionMap_tmul, ← hx]
    rw [← natCast_zsmul b n]
    rw [TensorProduct.tmul_smul]
    have he : (n : ℤ) • (n : ℚ)⁻¹ = 1 := by simp [zsmul_eq_mul, hne]
    exact congrArg (fun q : ℚ ↦ q ⊗ₜ[ℤ] b) he

/-- 概要：有理拡大の指定部分加群への全射性から整数倍の持ち上げを得る（定理 3.1）。
方針：部分加群の元の有理持ち上げに分母・ねじれ消去を適用する。
規約：部分加群は後で実際の G 不変部分として使う。有理降下を仮定せずに結論は出さない。
使われ方：不変部分への全次数比較の零次数から二つの K0 の整数形へ移す。 -/
theorem positive_multiple_of_rational_submodule_surjective (f : A →+ B)
    (N : Submodule ℤ (ℚ ⊗[ℤ] B))
    (hmap : ∀ t, rationalScalarExtensionMap f t ∈ N)
    (hsurj : Function.Surjective ((rationalScalarExtensionMap f).codRestrict N hmap))
    (b : B) (hb : 1 ⊗ₜ[ℤ] b ∈ N) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ n • b = f x := by
  obtain ⟨t, ht⟩ := hsurj ⟨1 ⊗ₜ[ℤ] b, hb⟩
  exact positive_multiple_of_rational_tensor_lift f b t (congrArg Subtype.val ht)

end SerrePositivity.KST.Descent
