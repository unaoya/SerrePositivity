module

public import SerrePositivity.CommutativeAlgebra.FiniteLengthValue

/-! # 有限長加群の部分商とスカラー倍

## 概要

有限長の加群 `W` の部分加群 `Z` からの全射 `Z ↠ H` があり、元 `c` が `H` を消すとき、
`H` の長さは `W / cW` の長さ以下である。

## 方針

`c` が `H` を消すので、全射は `Z / cZ` を経由する。有限長の加群の自己準同型では
核と余核の長さが等しいので `ℓ(Z / cZ) = ℓ(0 :_Z c)`。
`Z` は `W` に単射で入るので `0 :_Z c` は `0 :_W c` に単射で入り、
最後に再び `ℓ(0 :_W c) = ℓ(W / cW)` を使う。

## 使われ方

Tor を有限長の加群 `W ⊗ G_i` の部分商として表し、一様な零化元 `c` から
`ℓ Tor_i ≤ (rank G_i) · ℓ(W / cW)` を得るのに使う
（`formalization-plans/frobenius-koszul-elementary.md` の E1）。
環の局所性・Noether 性は要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 有限長の加群の自己準同型では、核と余核の長さが等しい。
核と像による分解と、像と余核による分解の二つで全体の長さを書き、像の長さを打ち消す。 -/
lemma length_ker_eq_length_quotient_range {M : Type u} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] M) (hM : IsFiniteLength R M) :
    Module.length R (LinearMap.ker f) = Module.length R (M ⧸ LinearMap.range f) := by
  have h₁ := lengthNat_ker_add_range f hM
  have h₂ := lengthNat_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) hM
  have hker : Module.length R (LinearMap.ker f) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (hM.of_injective (Submodule.subtype_injective _))
  have hquot : Module.length R (M ⧸ LinearMap.range f) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (hM.of_surjective (Submodule.mkQ_surjective _))
  rw [← ENat.natCast_toNat hker, ← ENat.natCast_toNat hquot]
  congr 1
  omega

/-- 有限長の加群 `W` に単射で入る `Z` から全射 `Z ↠ H` があり、`c` が `H` を消すなら、
`ℓ(H) ≤ ℓ(0 :_W c)`。全射は `Z / cZ` を経由し、`ℓ(Z / cZ) = ℓ(0 :_Z c) ≤ ℓ(0 :_W c)`。 -/
theorem length_le_length_ker_smul_of_subquotient
    {W Z H : Type u} [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
    [AddCommGroup H] [Module R H] (hW : IsFiniteLength R W)
    (ι : Z →ₗ[R] W) (hι : Function.Injective ι) (π : Z →ₗ[R] H) (hπ : Function.Surjective π)
    (c : R) (hc : ∀ x : H, c • x = 0) :
    Module.length R H ≤ Module.length R (LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)) := by
  have hZ : IsFiniteLength R Z := hW.of_injective hι
  -- 全射は `Z / cZ` を経由する
  have hle : LinearMap.range (c • LinearMap.id : Z →ₗ[R] Z) ≤ LinearMap.ker π := by
    rintro _ ⟨z, rfl⟩
    simp [hc]
  have h₁ : Module.length R H ≤
      Module.length R (Z ⧸ LinearMap.range (c • LinearMap.id : Z →ₗ[R] Z)) :=
    Module.length_le_of_surjective
      ((LinearMap.range (c • LinearMap.id : Z →ₗ[R] Z)).liftQ π hle)
      (by
        intro x
        obtain ⟨z, rfl⟩ := hπ x
        exact ⟨Submodule.Quotient.mk z, rfl⟩)
  -- `0 :_Z c` は `0 :_W c` に単射で入る
  have hker : LinearMap.ker (c • LinearMap.id : Z →ₗ[R] Z) ≤
      (LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)).comap ι := by
    intro z hz
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_comap] at hz ⊢
    rw [← map_smul, hz, map_zero]
  have h₂ : Module.length R (LinearMap.ker (c • LinearMap.id : Z →ₗ[R] Z)) ≤
      Module.length R (LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)) :=
    Module.length_le_of_injective
      ((ι.restrict hker))
      (by
        intro a b hab
        apply Subtype.ext
        apply hι
        exact congrArg Subtype.val hab)
  rw [← length_ker_eq_length_quotient_range _ hZ] at h₁
  exact h₁.trans h₂

/-- 有限長の加群 `W` に単射で入る `Z` から全射 `Z ↠ H` があり、`c` が `H` を消すなら、
`ℓ(H) ≤ ℓ(W / cW)`。`length_le_length_ker_smul_of_subquotient` と、核と余核の長さの一致による。 -/
theorem length_le_length_quotient_smul_of_subquotient
    {W Z H : Type u} [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
    [AddCommGroup H] [Module R H] (hW : IsFiniteLength R W)
    (ι : Z →ₗ[R] W) (hι : Function.Injective ι) (π : Z →ₗ[R] H) (hπ : Function.Surjective π)
    (c : R) (hc : ∀ x : H, c • x = 0) :
    Module.length R H ≤ Module.length R (W ⧸ LinearMap.range (c • LinearMap.id : W →ₗ[R] W)) := by
  rw [← length_ker_eq_length_quotient_range _ hW]
  exact length_le_length_ker_smul_of_subquotient hW ι hι π hπ c hc

/-- 有限個の直積上のスカラー倍の核は、各成分の核の直積と線形同値。 -/
def kerSmulPiEquiv (β : ℕ) (W : Type u) [AddCommGroup W] [Module R W] (c : R) :
    LinearMap.ker (c • LinearMap.id : (Fin β → W) →ₗ[R] (Fin β → W)) ≃ₗ[R]
      (Fin β → LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)) where
  toFun v j := ⟨v.1 j, by
    have h := congrFun (LinearMap.mem_ker.mp v.2) j
    rw [LinearMap.mem_ker]
    exact h⟩
  invFun w := ⟨fun j ↦ (w j).1, by
    rw [LinearMap.mem_ker]
    funext j
    exact LinearMap.mem_ker.mp (w j).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- 有限個の直積上のスカラー倍の核の長さは、成分の核の長さの `β` 倍。 -/
lemma length_ker_smul_pi (β : ℕ) (W : Type u) [AddCommGroup W] [Module R W] (c : R) :
    Module.length R (LinearMap.ker (c • LinearMap.id : (Fin β → W) →ₗ[R] (Fin β → W))) =
      β • Module.length R (LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)) := by
  rw [(kerSmulPiEquiv β W c).length_eq, Module.length_pi_of_fintype]
  simp

end SerrePositivity
