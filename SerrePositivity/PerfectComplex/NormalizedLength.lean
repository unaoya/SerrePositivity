module

public import SerrePositivity.CommutativeAlgebra.PowTorsion
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.RingTheory.Length

/-!
# 正規化長さ

論文 Lemma 2.3 と §3.4 冒頭の「正規化長さ」を抽象化する。
環 `C` の加群に `ℝ≥0∞` を対応させる関数で、イデアル `J` の冪で消える加群の短完全列で加法的、
同型で不変、零加群で `0` となるもの。値は無限でもよい（論文 §1.4 の規約）。

Lemma 2.3 の sup 性質 (2.3) は M2 で足す。

後半は、加法性と非負性から出る基本補題：部分加群・商・単射・全射に対する単調性、
`len M = len (ker f) + len (range f)`、完全列 `M → N → P` に対する `len N ≤ len M + len P`、
両端の長さが `0` なら中央も `0`、など。Lemma 3.4 の証明（`notes/lemma-3-4.md`）で使う。

通常の長さ `Module.length` は `J = ⊥` の正規化長さ `NormalizedLength.ordinary` である。
正規化長さによる Euler 評価（複体の `lambdaEuler`、`Tor` の `lambdaChi`）は
`PerfectComplex/NormalizedEuler.lean`。
-/

@[expose] public section

universe u

open scoped ENNReal

namespace SerrePositivity

/-- 環 `C` 上の正規化長さ。`J` の冪で消える加群の上で加法的な `ℝ≥0∞` 値関数。 -/
structure NormalizedLength (C : Type u) [CommRing C] (J : Ideal C) where
  /-- 加群の長さ。 -/
  len : (M : Type u) → [AddCommGroup M] → [Module C M] → ℝ≥0∞
  /-- 零加群の長さは `0`。 -/
  len_eq_zero_of_subsingleton : ∀ (M : Type u) [AddCommGroup M] [Module C M] [Subsingleton M],
    len M = 0
  /-- 同型な加群は同じ長さをもつ。 -/
  len_congr : ∀ (M N : Type u) [AddCommGroup M] [Module C M] [AddCommGroup N] [Module C N],
    (M ≃ₗ[C] N) → len M = len N
  /-- `J` の冪で消える加群の短完全列 `0 → M₁ → M₂ → M₃ → 0` で加法的。 -/
  len_add_of_exact : ∀ (M₁ M₂ M₃ : Type u) [AddCommGroup M₁] [Module C M₁]
    [AddCommGroup M₂] [Module C M₂] [AddCommGroup M₃] [Module C M₃]
    (f : M₁ →ₗ[C] M₂) (g : M₂ →ₗ[C] M₃),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
    (∃ n : ℕ, Module.IsTorsionBySet C M₂ (J ^ n : Ideal C)) →
    len M₂ = len M₁ + len M₃

namespace NormalizedLength

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)
variable {M N P : Type u} [AddCommGroup M] [Module C M] [AddCommGroup N] [Module C N]
  [AddCommGroup P] [Module C P]

/-- `len M = len N + len (M ⧸ N)`。 -/
lemma len_eq_add_quotient (hM : IsPowTorsion J M) (N : Submodule C M) :
    lam.len M = lam.len N + lam.len (M ⧸ N) :=
  lam.len_add_of_exact N M (M ⧸ N) N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N) hM

lemma len_submodule_le (hM : IsPowTorsion J M) (N : Submodule C M) : lam.len N ≤ lam.len M := by
  rw [lam.len_eq_add_quotient hM N]
  exact le_self_add

lemma len_quotient_le (hM : IsPowTorsion J M) (N : Submodule C M) :
    lam.len (M ⧸ N) ≤ lam.len M := by
  rw [lam.len_eq_add_quotient hM N]
  exact le_add_self

lemma len_le_of_injective (f : M →ₗ[C] N) (hf : Function.Injective f) (hN : IsPowTorsion J N) :
    lam.len M ≤ lam.len N := by
  rw [lam.len_congr M (LinearMap.range f) (LinearEquiv.ofInjective f hf)]
  exact lam.len_submodule_le hN _

lemma len_le_of_surjective (f : M →ₗ[C] N) (hf : Function.Surjective f) (hM : IsPowTorsion J M) :
    lam.len N ≤ lam.len M := by
  rw [← lam.len_congr _ _ (LinearMap.quotKerEquivOfSurjective f hf)]
  exact lam.len_quotient_le hM _

/-- `len M = len (ker f) + len (range f)`。 -/
lemma len_eq_add_ker_range (f : M →ₗ[C] N) (hM : IsPowTorsion J M) :
    lam.len M = lam.len (LinearMap.ker f) + lam.len (LinearMap.range f) := by
  rw [lam.len_eq_add_quotient hM (LinearMap.ker f)]
  congr 1
  exact lam.len_congr _ _ (LinearMap.quotKerEquivRange f)

lemma len_range_le (f : M →ₗ[C] N) (hM : IsPowTorsion J M) :
    lam.len (LinearMap.range f) ≤ lam.len M :=
  lam.len_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict hM

lemma len_range_eq_zero (f : M →ₗ[C] N) (hM : IsPowTorsion J M) (h : lam.len M = 0) :
    lam.len (LinearMap.range f) = 0 :=
  le_antisymm (h ▸ lam.len_range_le f hM) zero_le

/-- 完全列 `M →f N →g P` で `len N ≤ len M + len P`。 -/
lemma len_le_add_of_exact (f : M →ₗ[C] N) (g : N →ₗ[C] P) (h : Function.Exact f g)
    (hM : IsPowTorsion J M) (hN : IsPowTorsion J N) (hP : IsPowTorsion J P) :
    lam.len N ≤ lam.len M + lam.len P := by
  rw [lam.len_eq_add_ker_range g hN, LinearMap.exact_iff.mp h]
  exact add_le_add (lam.len_range_le f hM) (lam.len_submodule_le hP _)

/-- 完全列 `M → N → P` で両端の長さが `0` なら中央も `0`。 -/
lemma len_eq_zero_of_exact (f : M →ₗ[C] N) (g : N →ₗ[C] P) (h : Function.Exact f g)
    (hM : IsPowTorsion J M) (hN : IsPowTorsion J N) (hP : IsPowTorsion J P)
    (h1 : lam.len M = 0) (h3 : lam.len P = 0) : lam.len N = 0 := by
  have := lam.len_le_add_of_exact f g h hM hN hP
  rw [h1, h3, add_zero] at this
  exact le_antisymm this zero_le

/-- 完全列 `M → N → P` で両端の長さが有限なら中央も有限。 -/
lemma len_ne_top_of_exact (f : M →ₗ[C] N) (g : N →ₗ[C] P) (h : Function.Exact f g)
    (hM : IsPowTorsion J M) (hN : IsPowTorsion J N) (hP : IsPowTorsion J P)
    (h1 : lam.len M ≠ ⊤) (h3 : lam.len P ≠ ⊤) : lam.len N ≠ ⊤ :=
  ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨h1, h3⟩) (lam.len_le_add_of_exact f g h hM hN hP)

/-- 完全列 `M →f N →g P → 0` で `len (ker f) = 0` なら `len N = len M + len P`。 -/
lemma len_eq_add_of_exact_of_surjective (f : M →ₗ[C] N) (g : N →ₗ[C] P)
    (h : Function.Exact f g) (hg : Function.Surjective g)
    (hM : IsPowTorsion J M) (hN : IsPowTorsion J N)
    (hker : lam.len (LinearMap.ker f) = 0) : lam.len N = lam.len M + lam.len P := by
  rw [lam.len_eq_add_ker_range g hN, LinearMap.exact_iff.mp h, LinearMap.range_eq_top.mpr hg,
    lam.len_eq_add_ker_range f hM, hker, zero_add]
  congr 1
  exact lam.len_congr _ _ Submodule.topEquiv

/-- 定義域のイデアルの取り替え：`J'` 冪ねじれなら `J` 冪ねじれ、のとき `J'` 版の正規化長さを得る。 -/
def restrict (lam : NormalizedLength C J) (J' : Ideal C)
    (h : ∀ (M : Type u) [AddCommGroup M] [Module C M], IsPowTorsion J' M → IsPowTorsion J M) :
    NormalizedLength C J' where
  len := lam.len
  len_eq_zero_of_subsingleton := lam.len_eq_zero_of_subsingleton
  len_congr := lam.len_congr
  len_add_of_exact := by
    intro M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg hM₂
    exact lam.len_add_of_exact M₁ M₂ M₃ f g hf hg hfg (h M₂ hM₂)

@[simp] lemma restrict_len (lam : NormalizedLength C J) (J' : Ideal C) (h) (M : Type u)
    [AddCommGroup M] [Module C M] : (lam.restrict J' h).len M = lam.len M := rfl

/-- 通常の長さ `Module.length` は `J = ⊥` の正規化長さ（`ℕ∞` を `ℝ≥0∞` に埋め込む）。
`IsPowTorsion ⊥ M` はどの `M` でも成り立つ（`IsPowTorsion.bot`）ので、正規化長さについての
Euler 評価の定理はすべて通常の長さに特殊化できる（`NormalizedEuler.lean`、`OrdinaryEuler.lean`）。 -/
noncomputable def ordinary (T : Type u) [CommRing T] : NormalizedLength T ⊥ where
  len := by
    intro M _ _
    exact (Module.length T M : ℝ≥0∞)
  len_eq_zero_of_subsingleton := by
    intro M _ _ _
    simp [Module.length_eq_zero]
  len_congr := by
    intro M N _ _ _ _ e
    rw [e.length_eq]
  len_add_of_exact := by
    intro M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg _
    rw [Module.length_eq_add_of_exact f g hf hg hfg, ENat.toENNReal_add]

@[simp] lemma ordinary_len (T : Type u) [CommRing T] (M : Type u) [AddCommGroup M]
    [Module T M] : (ordinary T).len M = (Module.length T M : ℝ≥0∞) := rfl

end NormalizedLength

end SerrePositivity
