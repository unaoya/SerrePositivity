module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.CommutativeAlgebra.ConductorQuotient
public import SerrePositivity.PerfectComplex.NormalizedLength
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# 商写像の核とテンソル積の正規化長さ

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

- `len_ker_quotientToExtension_le`：共通分母の条件から商写像の核の長さを、
  分母倍写像の余核の長さで評価する（定理2.5の核の評価）。

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

variable {D C : Type u} [CommRing D] [CommRing C] [Algebra D C]

/-- 係数環のイデアルの冪で消える商は、代数を拡大しても同じ冪で消える。
元の商で単位元を消すことから、係数の像がイデアルに入ると分かる。
平坦性や有限生成性は必要ない。 -/
lemma isPowTorsion_quotient_extension (R : Type u) [CommRing R]
    [Algebra R D] [Algebra R C] [IsScalarTower R D C]
    (J : Ideal R) (I : Ideal D) (hI : IsPowTorsion J (D ⧸ I)) :
    IsPowTorsion J (C ⧸ I.map (algebraMap D C)) := by
  obtain ⟨k, hk⟩ := hI
  refine ⟨k, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hk ⊢
  intro r hr
  simp only [SetLike.mem_coe, Module.mem_annihilator]
  intro x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hz := (Module.mem_annihilator.mp (hk hr)) (1 : D ⧸ I)
  have hm : algebraMap R D r ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply R D (D ⧸ I),
      Ideal.Quotient.algebraMap_eq] using hz
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [IsScalarTower.algebraMap_apply R D C]
  exact Ideal.mul_mem_right c _ (Ideal.mem_map_of_mem _ hm)

/-- `D` 加群 `M` がイデアル `J` の `n` 乗で消えるなら `C ⊗_D M` は `(J C)^n` で消える。 -/
lemma isPowTorsion_tensorProduct_of_isTorsionBySet (J : Ideal D) (M : Type u) [AddCommGroup M]
    [Module D M] {n : ℕ} (hM : Module.IsTorsionBySet D M (J ^ n : Ideal D)) :
    IsPowTorsion (J.map (algebraMap D C)) (C ⊗[D] M) := by
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

/-- 共通分母による商写像の核の正規化長さの評価。
長さを測る基底 `R` は `D` と別に取れるので、塔上の正規化長さにも適用できる。
`g` 倍写像の余核を `D/(I,g)` と同定して、右辺を通常の商の長さで表す。 -/
theorem len_ker_quotientToExtension_le (R : Type u) [CommRing R]
    [Algebra R D] [Algebra R C] [IsScalarTower R D C]
    {J : Ideal R} (lam : NormalizedLength R J)
    (hinj : Function.Injective (algebraMap D C)) (I : Ideal D) (g : D)
    (hg : ∀ c : C, ∃ d : D, algebraMap D C d = algebraMap D C g * c)
    (htors : IsPowTorsion J (D ⧸ I)) (hfinite : lam.len (D ⧸ I) ≠ ⊤) :
    lam.len (LinearMap.ker ((quotientToExtension (C := C) I).toLinearMap.restrictScalars R)) ≤
      lam.len (D ⧸ (I ⊔ Ideal.span {g})) := by
  rw [← lam.len_congr _ _ (quotientSmulCokerEquiv R I g)]
  apply lam.len_ker_le_len_coker_of_ker_le _ _ htors hfinite
  intro x hx
  exact smul_eq_zero_of_quotientToExtension_eq_zero hinj I g hg x hx

variable [IsLocalRing D]

/-- `D` 加群 `M` が `m_D^n` で消えるなら `C ⊗_D M` は `(m_D C)^n` で消える。 -/
lemma isPowTorsion_tensorProduct (M : Type u) [AddCommGroup M] [Module D M] {n : ℕ}
    (hM : Module.IsTorsionBySet D M ((maximalIdeal D) ^ n : Ideal D)) :
    IsPowTorsion ((maximalIdeal D).map (algebraMap D C)) (C ⊗[D] M) :=
  isPowTorsion_tensorProduct_of_isTorsionBySet (maximalIdeal D) M hM

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
