module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.PerfectComplex.NormalizedLength
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# 有限長加群のテンソル積の正規化長さ（論文 Corollary 2.6 (3) の中身）

## 概要

局所環 `D`、`D` 代数 `C`、`m_D C` 冪ねじれ加群の上の正規化長さ `λ` について、有限長 `D` 加群 `N` で

  `λ(C ⊗_D N) ≤ ℓ_D(N) · λ(C ⊗_D (D/m_D))`。

論文 Corollary 2.6 の 3 番目の主張の証明（p.9）そのもの：`N` の組成列を `C` でテンソルすると、
右完全性からフィルトレーションができ、各因子は `C/m_D C` の商になる。`N = D/H`（`H` は
パラメータイデアル）で `C ⊗_D (D/H) ≃ C/HC` を使えば

  `λ(C/HC) ≤ ℓ(D/H) · λ(C/m_D C)`

となり、Theorem 2.5 の (2.5) から `0 < λ(C/HC)` なので `0 < λ(C/m_D C)` が出る
（`Paper/Section2/Corollary2_6.lean`）。

## 内容

- `isPowTorsion_tensorProduct`：`m_D^n` で消える `D` 加群との `C` 上のテンソル積は `(m_D C)^n` で
  消える。
- `len_tensorProduct_le_length_mul`：上の不等式（`IsFiniteLength` の帰納法と
  `TensorProduct.lTensor_exact`）。
- `len_quotient_map_le_length_mul`：`N = D/H` の形。
- `len_quotient_maximalIdeal_pos`：`0 < λ(C/HC)`、`ℓ(D/H) < ∞` なら `0 < λ(C/m_D C)`。
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity

variable {D C : Type u} [CommRing D] [IsLocalRing D] [CommRing C] [Algebra D C]

/-- `D` 加群 `M` が `m_D^n` で消えるなら `C ⊗_D M` は `(m_D C)^n` で消える。 -/
lemma isPowTorsion_tensorProduct (M : Type u) [AddCommGroup M] [Module D M] {n : ℕ}
    (hM : Module.IsTorsionBySet D M ((maximalIdeal D) ^ n : Ideal D)) :
    IsPowTorsion ((maximalIdeal D).map (algebraMap D C)) (C ⊗[D] M) := by
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, ← Ideal.map_pow, SetLike.coe_subset_coe,
    Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro x
  refine TensorProduct.inductionOn x (fun c m ↦ ?_)
    (fun x y hx hy ↦ by rw [smul_add, hx, hy, add_zero])
  rw [algebraMap_smul, ← TensorProduct.tmul_smul]
  have : a • m = 0 := hM (x := m) (a := ⟨a, ha⟩)
  rw [this, TensorProduct.tmul_zero]

/-- 有限長 `D` 加群 `M` について `C ⊗_D M` は `m_D C` 冪ねじれ。 -/
lemma isPowTorsion_tensorProduct_of_isFiniteLength (M : Type u) [AddCommGroup M] [Module D M]
    (hM : IsFiniteLength D M) :
    IsPowTorsion ((maximalIdeal D).map (algebraMap D C)) (C ⊗[D] M) := by
  obtain ⟨n, hn⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hM
  exact isPowTorsion_tensorProduct M hn

variable (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))

/-- **組成列による評価**：有限長 `D` 加群 `M` で `λ(C ⊗_D M) ≤ ℓ_D(M) · λ(C ⊗_D (D/m_D))`。 -/
theorem len_tensorProduct_le_length_mul (M : Type u) [AddCommGroup M] [Module D M]
    (hM : IsFiniteLength D M) :
    lam.len (C ⊗[D] M) ≤
      (Module.length D M : ℝ≥0∞) * lam.len (C ⊗[D] (D ⧸ maximalIdeal D)) := by
  induction hM with
  | of_subsingleton =>
    rename_i M _ _ _
    have : Subsingleton (C ⊗[D] M) := by
      refine ⟨fun x y ↦ ?_⟩
      have h0 : ∀ z : C ⊗[D] M, z = 0 := by
        intro z
        refine TensorProduct.inductionOn z (fun c m ↦ ?_) (fun x y hx hy ↦ by rw [hx, hy, add_zero])
        rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
      rw [h0 x, h0 y]
    rw [lam.len_eq_zero_of_subsingleton]
    exact zero_le
  | @of_simple_quotient M _ _ N _ hN ih =>
    have hMfl : IsFiniteLength D M := IsFiniteLength.of_simple_quotient hN
    have hQfl : IsFiniteLength D (M ⧸ N) := hMfl.of_surjective N.mkQ_surjective
    -- `C ⊗ N → C ⊗ M → C ⊗ (M/N)` は完全
    have hex : Function.Exact (N.subtype.baseChange C) (N.mkQ.baseChange C) := by
      have := lTensor_exact C (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
      rwa [← LinearMap.baseChange_eq_lTensor, ← LinearMap.baseChange_eq_lTensor] at this
    have h1 := lam.len_le_add_of_exact _ _ hex
      (isPowTorsion_tensorProduct_of_isFiniteLength N hN)
      (isPowTorsion_tensorProduct_of_isFiniteLength M hMfl)
      (isPowTorsion_tensorProduct_of_isFiniteLength _ hQfl)
    -- `C ⊗ (M/N) ≃ C ⊗ (D/m)`
    obtain ⟨e⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := D) (M := M ⧸ N)
    have h2 : lam.len (C ⊗[D] (M ⧸ N)) = lam.len (C ⊗[D] (D ⧸ maximalIdeal D)) :=
      lam.len_congr _ _ (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) e)
    rw [h2] at h1
    refine h1.trans ?_
    rw [Module.length_eq_succ_of_isSimpleModule_quotient N, ENat.toENNReal_add,
      ENat.toENNReal_one, add_mul, one_mul]
    exact add_le_add ih le_rfl

/-- `N = D/H` の形：`λ(C/HC) ≤ ℓ_D(D/H) · λ(C/m_D C)`。 -/
theorem len_quotient_map_le_length_mul (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H)) :
    lam.len (C ⧸ H.map (algebraMap D C)) ≤
      (Module.length D (D ⧸ H) : ℝ≥0∞) *
        lam.len (C ⧸ (maximalIdeal D).map (algebraMap D C)) := by
  have e1 := lam.len_congr _ _
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C H).toLinearEquiv
  have e2 := lam.len_congr _ _
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (maximalIdeal D)).toLinearEquiv
  rw [e1, e2]
  exact len_tensorProduct_le_length_mul lam _ hH

/-- `0 < λ(C/HC)` で `ℓ(D/H) < ∞` なら `0 < λ(C/m_D C)`（Corollary 2.6 (3) の最後の一歩）。 -/
theorem len_quotient_maximalIdeal_pos (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H))
    (hpos : 0 < lam.len (C ⧸ H.map (algebraMap D C))) :
    0 < lam.len (C ⧸ (maximalIdeal D).map (algebraMap D C)) := by
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  have := len_quotient_map_le_length_mul lam H hH
  rw [h0, mul_zero] at this
  exact absurd (le_antisymm this zero_le) hpos.ne'

end SerrePositivity
