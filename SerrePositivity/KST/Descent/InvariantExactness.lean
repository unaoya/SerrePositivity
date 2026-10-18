module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Tactic.NormNum

/-!
# 有限群の有理不変部分の完全性

## 概要
有限群の有理表現の同変な完全列は、不変部分を取った後も完全。

## 方針
Mathlib の平均作用素を用い、核の元の任意の持ち上げを平均して不変な持ち上げにする。

## 規約
通常の不変部分についての主張。hG や π_n(hG) との比較は L9 の実構成に接続する。
表現の加群の有限次元性・有限生成性・次数の有界性は要求しない。

## 使われ方
論文 定理 3.1 の軌道正方形、(3.8)、有理固定点の全次数の長完全列。
-/

@[expose] public section

namespace SerrePositivity.KST.Descent

open Representation

section Maps

variable {G M N : Type*} [Group G]
variable [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
variable {ρ : Representation ℚ G M} {σ : Representation ℚ G N}

/-- 概要：自明な表現の不変部分は元の有理加群（論文 (3.8) の π_* 側）。
方針：包含の逆に、全要素が固定されることを使う。
規約：hG との比較や群の有限性はこの代数的計算には不要。
使われ方：section の安定化部分群の自明作用に対する Shapiro 計算。 -/
noncomputable def trivialInvariantsEquiv (ρ : Representation ℚ G M) [ρ.IsTrivial] :
    ρ.invariants ≃ₗ[ℚ] M where
  toFun x := x.val
  invFun x := ⟨x, fun g ↦ ρ.isTrivial_apply g x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 概要：同変線形写像を不変部分へ制限する（論文 (3.7)–(3.8)）。
方針：同変性により不変元の像が不変になることを使う。
規約：通常の不変部分。群の有限性は写像の定義には不要。
使われ方：軌道正方形の長完全列から不変部分の列を作る。 -/
noncomputable def invariantMap (f : IntertwiningMap ρ σ) : ρ.invariants →ₗ[ℚ] σ.invariants :=
  (f.toLinearMap.comp ρ.invariants.subtype).codRestrict _ fun x g ↦ by
    change σ g (f x.val) = f x.val
    rw [← f.isIntertwining, x.property g]

/-- 概要：不変部分への制限は元の写像を評価する（論文 (3.7) の指定比較）。
方針：値域制限の定義を展開する。
規約：不変性の証明項は値に影響しない。
使われ方：平均持ち上げと完全性の計算。 -/
@[simp] theorem invariantMap_apply_val (f : IntertwiningMap ρ σ) (x : ρ.invariants) :
    (invariantMap f x).val = f x.val := rfl

/-- 概要：単射な同変写像の不変部分への制限は単射（論文 定理 3.1）。
方針：部分型の値を元の単射に入れる。
規約：この片側の完全性には群の有限性も有理化も不要。
使われ方：不変部分の長完全列の端の単射性。 -/
theorem invariantMap_injective (f : IntertwiningMap ρ σ) (hf : Function.Injective f) :
    Function.Injective (invariantMap f) := by
  intro x y h
  apply Subtype.ext
  exact hf (congrArg Subtype.val h)

/-- 概要：平均作用素は同変線形写像に自然（論文 定理 3.1、(3.8)）。
方針：Mathlib の群環による平均を展開し、有限和の各項に同変性を使う。
規約：群の位数が可逆であることを型の仮定に明示する。
使われ方：任意の持ち上げを平均してもその像を保つ。 -/
theorem averageMap_naturality [Fintype G] [Invertible (Fintype.card G : ℚ)]
    (f : IntertwiningMap ρ σ) (x : M) :
    f (ρ.averageMap x) = σ.averageMap (f x) := by
  simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
    Representation.asAlgebraHom_of, LinearMap.smul_apply, LinearMap.sum_apply,
    f.isIntertwining]

/-- 概要：有限群の有理表現の全射は不変部分でも全射（論文 定理 3.1）。
方針：任意の持ち上げを平均し、平均の自然性と不変元上の恒等性を使う。
規約：加群の有限次元性や次数の有界性を仮定しない。
使われ方：全次数の長完全列に不変部分を適用する完全性の中核。 -/
theorem invariantMap_surjective [Finite G]
    (f : IntertwiningMap ρ σ) (hf : Function.Surjective f) :
    Function.Surjective (invariantMap f) := by
  let := Fintype.ofFinite G
  let : Invertible (Fintype.card G : ℚ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  intro y
  obtain ⟨x, hx⟩ := hf y.val
  refine ⟨⟨ρ.averageMap x, ρ.averageMap_invariant x⟩, ?_⟩
  apply Subtype.ext
  change f (ρ.averageMap x) = y.val
  rw [averageMap_naturality, hx, σ.averageMap_id y.val y.property]

end Maps

section Exactness

variable {G M N P : Type*} [Group G] [Finite G]
variable [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
variable [AddCommGroup P] [Module ℚ P]
variable {ρ : Representation ℚ G M} {σ : Representation ℚ G N}
variable {τ : Representation ℚ G P}

/-- 概要：有限群の有理不変部分は同変な完全列を保つ（論文 定理 3.1、(3.8)）。
方針：核の不変元を元の完全性で持ち上げ、その持ち上げを平均する。
規約：長完全列の任意の隣接二射へ適用でき、次数の有界性は不要。
使われ方：軌道正方形に対する π_* 長完全列の有理不変部分。 -/
theorem invariantMap_exact (f : IntertwiningMap ρ σ) (g : IntertwiningMap σ τ)
    (h : Function.Exact f g) : Function.Exact (invariantMap f) (invariantMap g) := by
  let := Fintype.ofFinite G
  let : Invertible (Fintype.card G : ℚ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  intro y
  constructor
  · intro hy
    have hy' : g y.val = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (h y.val).mp hy'
    refine ⟨⟨ρ.averageMap x, ρ.averageMap_invariant x⟩, ?_⟩
    apply Subtype.ext
    change f (ρ.averageMap x) = y.val
    rw [averageMap_naturality, hx, σ.averageMap_id y.val y.property]
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact h.apply_apply_eq_zero x.val

end Exactness

end SerrePositivity.KST.Descent
