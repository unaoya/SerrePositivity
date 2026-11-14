module

public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # 有限生成自由分解による Tor の長さの評価

## 概要

`W` を有限長の加群、`K` を `M` の射影分解で、次数 `-i` の項が階数 `β` の自由加群とする。
元 `c` が `Tor_i^R(W, M)` を消すなら、`ℓ Tor_i^R(W, M) ≤ β · ℓ(W / cW)`。

## 方針

`Tor_i(W, M)` は複体 `W ⊗ K` の次数 `-i` のホモロジーで、その輪体は
`W ⊗ K_{-i} ≅ W^β` に単射で入り、ホモロジーへ全射する。`W^β` は有限長なので、
有限長の加群の部分商の評価（`length_le_length_ker_smul_of_subquotient`）が使え、
`ℓ(0 :_{W^β} c) = β · ℓ(0 :_W c) = β · ℓ(W / cW)` となる。

## 使われ方

Paper Theorem 2.5 の式 (2.4) の等標数部分で、高次 Koszul ホモロジーの消滅に用いる有限長の一様な上界。
`W = R'/(Z^q)` とし、`K` を `q` によらない有限生成自由分解にとれば、
一様な零化元 `c` から `q` によらない係数 `β` で長さを抑えられる。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- **有限長の加群を第1変数とする Tor の評価**：`W` は有限長、`K` は `M` の射影分解で、
`K_{-i}` は階数 `β` の自由加群とする。`c` が `Tor_i(W, M)` を消すなら
`ℓ Tor_i(W, M) ≤ β · ℓ(W / cW)`。輪体を `W ⊗ K_{-i} ≅ W^β` に入れて部分商の評価を使う。 -/
theorem length_torModule_le_of_smul_eq_zero (W M : Type u) [AddCommGroup W] [Module R W]
    [AddCommGroup M] [Module R M] (hW : IsFiniteLength R W)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsResolutionOf K (ModuleCat.of R M)) (i : ℕ)
    (β : ℕ) (e : K.X (-(i : ℤ)) ≃ₗ[R] (Fin β → R)) (c : R)
    (hc : ∀ x : TorModule R i W M, c • x = 0) :
    Module.length R (TorModule R i W M) ≤
      β • Module.length R (W ⧸ LinearMap.range (c • LinearMap.id : W →ₗ[R] W)) := by
  let Q :=
    (((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R W)).mapHomologicalComplex _).obj K
  let φ := torModuleIsoCochain W hK i
  -- ホモロジーへ移した零化
  have hcH : ∀ y : Q.homology (-(i : ℤ)), c • y = 0 := by
    intro y
    have h := hc (φ.inv.hom y)
    have : φ.hom.hom (φ.inv.hom y) = y := by
      change (φ.inv ≫ φ.hom).hom y = y
      rw [φ.inv_hom_id]
      rfl
    rw [← this, ← map_smul, h, map_zero]
  -- 次数 `-i` の項を `W^β` と同一視する
  let eX : Q.X (-(i : ℤ)) ≃ₗ[R] (Fin β → W) :=
    ((TensorProduct.congr (LinearEquiv.refl R W) e).trans
      (TensorProduct.piScalarRight R R W (Fin β)))
  have hWβ : IsFiniteLength R (Fin β → W) := by
    rw [← Module.length_ne_top_iff, Module.length_pi_of_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (Module.length_ne_top_iff.mpr hW)
  have hι : Function.Injective (eX.toLinearMap ∘ₗ (Q.iCycles (-(i : ℤ))).hom) :=
    eX.injective.comp ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have hπ : Function.Surjective (Q.homologyπ (-(i : ℤ))).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hH := length_le_length_ker_smul_of_subquotient hWβ _ hι _ hπ c hcH
  rw [length_ker_smul_pi, length_ker_eq_length_quotient_range _ hW] at hH
  rw [φ.toLinearEquiv.length_eq]
  exact hH

end SerrePositivity
