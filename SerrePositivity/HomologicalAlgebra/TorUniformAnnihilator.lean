module

public import SerrePositivity.HomologicalAlgebra.TorLES
public import SerrePositivity.HomologicalAlgebra.Resolution
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # 有限生成加群の高次 Tor を一様に消す元

## 概要

整域 `R` 上の有限生成加群 `M` には、零でない元 `c` で、任意の加群 `N` と `i ≥ 1` について
`Tor_i^R(N, M)` を消すものがある。

## 方針

一般点の基底から有限階数の自由部分加群 `F ↪ M` をとると、余核 `M / F` は階数零、
つまりねじれ加群になる。有限生成なので、零でない一つの元 `c` が余核全体を消す。
Tor の長完全列で `Tor_i(N, F) = 0`（`i ≥ 1`）なので `Tor_i(N, M) → Tor_i(N, M / F)` は単射で、
右辺は `c` で消える。

## 使われ方

Paper Theorem 2.5 の式 (2.4) の等標数部分で、高次 Koszul ホモロジーの消滅に用いるTor の一様な零化。
パラメータ Koszul 複体の高次ホモロジーを一様な元で消し、有限長の加群の中での評価に渡す。
`M` の捩れのなさ・局所性・Noether 性は要求しない。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 第2変数の加群 `T` を `a` が消すなら、`a` は `Tor_i^R(N, T)` を消す。
テンソル関手のスカラー倍との両立を、一般の左導来関手の零化の定理に適用する。 -/
theorem torModule_smul_eq_zero (i : ℕ) (N T : Type u) [AddCommGroup N] [Module R N]
    [AddCommGroup T] [Module R T] (a : R) (ha : ∀ t : T, a • t = 0)
    (x : TorModule R i N T) : a • x = 0 :=
  leftDerived_smul_eq_zero (RingHom.id R) ((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R N))
    (fun a f => MonoidalLinear.whiskerLeft_smul _ a f) i (ModuleCat.of R T) a ha x

/-- 有限階数の自由加群を第2変数とする高次 Tor は零。 -/
theorem torModule_free_succ_eq_zero (i n : ℕ) (N : Type u) [AddCommGroup N] [Module R N]
    (x : TorModule R (i + 1) N (Fin n → R)) : x = 0 := by
  have : Projective (ModuleCat.of R (Fin n → R)) :=
    ModuleCat.projective_of_free (Pi.basisFun R (Fin n))
  have hz := isZero_Tor_succ_of_projective (C := ModuleCat.{u} R) (ModuleCat.of R N)
    (ModuleCat.of R (Fin n → R)) i
  exact @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.mp hz) x 0

variable [IsDomain R]

/-- **一様な零化元**：整域上の有限生成加群 `M` には、零でない `c` で、任意の `N` と `i ≥ 1` について
`Tor_i^R(N, M)` を消すものがある。一般点の基底による自由部分加群の余核はねじれ加群で、
その零化元が `Tor_i(N, M) ↪ Tor_i(N, M / F)` を通して高次 Tor を消す。 -/
theorem exists_ne_zero_smul_torModule_eq_zero (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ c : R, c ≠ 0 ∧ ∀ (N : Type u) [AddCommGroup N] [Module R N] (i : ℕ)
      (x : TorModule R (i + 1) N M), c • x = 0 := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) le_rfl
  let g := Fintype.linearCombination R v
  have hg : Function.Injective g := linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  -- 余核はねじれ加群
  have hr : Module.finrank R (LinearMap.range g) = Module.finrank R M := by
    rw [← (LinearEquiv.ofInjective g hg).finrank_eq]
    simp
  have hz : Module.finrank R (M ⧸ LinearMap.range g) = 0 := by
    have := Module.finrank_quotient_add_finrank_le (LinearMap.range g)
    rw [hr] at this
    omega
  have ht := Module.finrank_eq_zero_iff_isTorsion.mp hz
  obtain ⟨c, hcann, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  have hc : ∀ q : M ⧸ LinearMap.range g, c • q = 0 := fun q ↦
    (Submodule.mem_annihilator.mp hcann) q Submodule.mem_top
  refine ⟨c, nonZeroDivisors.ne_zero hc0, ?_⟩
  intro N _ _ i x
  obtain ⟨α, β, δ, hαβ, -, -, -⟩ := torModule_longExact N g (LinearMap.range g).mkQ hg
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range g)
  -- `Tor_{i+1}(N, F) = 0` なので `β` は単射
  have hβ : Function.Injective (β (i + 1)) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨w, rfl⟩ := (hαβ (i + 1) y).mp hy
    rw [torModule_free_succ_eq_zero i _ N w, map_zero]
  apply hβ
  rw [map_smul, map_zero]
  exact torModule_smul_eq_zero (i + 1) N _ c hc _

end SerrePositivity
