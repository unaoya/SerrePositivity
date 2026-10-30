module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # イデアルやスカラーの冪で消える加群

## 概要

加群 M がイデアル J のある冪で消えること `IsPowTorsion J M` を定め、単射・全射・同型・部分加群・商で保たれること、根基が零化イデアルを含めば成り立つことを示す。スカラー a の冪ねじれがすべて a^N で消えるとき、a^N の核で割ると a は正則に作用する。平坦加群には、スカラーの零化の上界と冪商上のねじれの一様な制御が移る。

## 方針

冪ねじれは零化イデアルが J の冪を含むことで書き、Noether 性・有限性・元の環の正則性は仮定しない。平坦加群への移送は、核の関係式をテンソルして平坦性で保つ。

## 規約

`IsPowTorsion` は正規化長さ（PerfectComplex/NormalizedLength）の定義域を与えるので名前を変えない。`bounded_power_torsion_decomposition` は未使用の候補（refactor-plan §2.8）。

## 使われ方

PerfectComplex の台と正規化長さ、HomologicalAlgebra の Tor の有限長と導来完備化の冪ねじれの塔、`PowerTorsion/Category`、Almost。
-/

@[expose] public noncomputable section

universe u

section PowTorsionPart

namespace SerrePositivity

/-- `M` がイデアル `J` のある冪で消えること：`J^n M = 0` となる `n` がある。Mathlib の
`Module.IsTorsionBySet`（集合の元すべてが `M` を消す）を `J^n` に適用した形で、`J^n ⊆ Ann M` と
同値である。正規化長さ `NormalizedLength C J` の定義域の条件。 -/
abbrev IsPowTorsion {C : Type u} [CommRing C] (J : Ideal C) (M : Type u) [AddCommGroup M]
    [Module C M] : Prop :=
  ∃ n : ℕ, Module.IsTorsionBySet C M (J ^ n : Ideal C)

namespace IsPowTorsion

variable {C : Type u} [CommRing C] {J : Ideal C} {M N : Type u} [AddCommGroup M] [Module C M]
  [AddCommGroup N] [Module C N]

/-- `N` が `J` の冪で消え、`f : M → N` が単射なら、`M` も同じ冪で消える。単射なら零化イデアルは
大きくなる（`Ann N ⊆ Ann M`）ことによる。 -/
lemma of_injective (f : M →ₗ[C] N) (hf : Function.Injective f) (hN : IsPowTorsion J N) :
    IsPowTorsion J M := by
  obtain ⟨n, hn⟩ := hN
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hn ⊢
  exact hn.trans (f.annihilator_le_of_injective hf)

/-- `M` が `J` の冪で消え、`f : M → N` が全射なら、`N` も同じ冪で消える。全射なら零化イデアルは
大きくなる（`Ann M ⊆ Ann N`）ことによる。 -/
lemma of_surjective (f : M →ₗ[C] N) (hf : Function.Surjective f) (hM : IsPowTorsion J M) :
    IsPowTorsion J N := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hn ⊢
  exact hn.trans (f.annihilator_le_of_surjective hf)

/-- 線形同値 `e : M ≃ N` で冪ねじれの条件は移る（`of_surjective` の特別な場合）。 -/
lemma of_equiv (e : M ≃ₗ[C] N) (hM : IsPowTorsion J M) : IsPowTorsion J N :=
  of_surjective e.toLinearMap e.surjective hM

/-- 冪ねじれ加群の部分加群は、同じ冪で消える（包含が単射）。 -/
lemma submodule (hM : IsPowTorsion J M) (N : Submodule C M) : IsPowTorsion J N :=
  of_injective N.subtype N.injective_subtype hM

/-- 冪ねじれ加群の商加群は、同じ冪で消える（商への射影が全射）。 -/
lemma quotient (hM : IsPowTorsion J M) (N : Submodule C M) : IsPowTorsion J (M ⧸ N) :=
  of_surjective N.mkQ N.mkQ_surjective hM

/-- 零加群はどんなイデアルについても冪ねじれである（`n = 0`、`J^0 = ⊤` でも零加群は消える）。 -/
lemma of_subsingleton [Subsingleton M] : IsPowTorsion J M :=
  ⟨0, fun _ _ ↦ Subsingleton.elim _ _⟩

/-- `J = ⊥` のときはどの加群も冪ねじれである：`⊥^1 = ⊥` で、`0 • x = 0` だから。通常の長さ
`Module.length` を `J = ⊥` の正規化長さ `NormalizedLength.ordinary` とみなし、正規化長さの一般定理
（写像錐についての加法性など）を通常の長さに特殊化するときに、ねじれの仮定をこれで満たす
（`PerfectComplex/OrdinaryEuler.lean`）。 -/
lemma bot : IsPowTorsion (⊥ : Ideal C) M :=
  ⟨1, fun _ a ↦ by
    have ha : (a : C) = 0 := by simpa using a.2
    rw [ha, zero_smul]⟩

/-- `J` が有限生成で `J ⊆ √(Ann M)`（`J` の各元のある冪が `M` を消す）なら、`J` のある冪が `M` を
消す。有限個の生成元それぞれの冪が `Ann M` に入るので、十分大きい冪で `J^n ⊆ Ann M` となる
（Mathlib の `Ideal.exists_pow_le_of_le_radical_of_fg`）。台をもつ複体のホモロジーが冪ねじれで
あること（`PerfectComplex/Support.lean`、`PerfectComplex/NormalizedEuler.lean`）に使う。 -/
lemma of_le_radical_annihilator (hfg : J.FG) (h : J ≤ (Module.annihilator C M).radical) :
    IsPowTorsion J M := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h hfg
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  exact hn

end IsPowTorsion

/-- 環の塔 `A → T → C` と、`A` のイデアル `I`、`T` のイデアル `J` について、`J^N ⊆ I T` なら、
`I C` の冪で消える `C` 加群は `J C` の冪でも消える：`(J C)^{N n} = (J^N) C ⊆ (I T) C = I C` の `n` 乗が
`M` を消すから。論文で正規化長さ `λ` の定義域を `m_D C` から `m_A C` に取り替えるとき
（`A ⊆ D` が有限なら `m_D^N ⊆ m_A D`、`LocalAlgebra.lean` の `maximalIdeal_pow_le_map_of_finite`）に、
`NormalizedLength.restrict` と組み合わせて使う。 -/
lemma IsPowTorsion.of_pow_le {A T C : Type u} [CommRing A] [CommRing T] [CommRing C]
    [Algebra A T] [Algebra T C] [Algebra A C] [IsScalarTower A T C] {I : Ideal A} {J : Ideal T}
    (hN : ∃ N : ℕ, J ^ N ≤ I.map (algebraMap A T)) (M : Type u) [AddCommGroup M] [Module C M]
    (hM : IsPowTorsion (I.map (algebraMap A C)) M) : IsPowTorsion (J.map (algebraMap T C)) M := by
  obtain ⟨N, hN⟩ := hN
  obtain ⟨n, hn⟩ := hM
  refine ⟨N * n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hn ⊢
  refine Set.Subset.trans ?_ hn
  rw [SetLike.coe_subset_coe, pow_mul, ← Ideal.map_pow]
  refine Ideal.pow_right_mono ?_ n
  calc (J ^ N).map (algebraMap T C) ≤ (I.map (algebraMap A T)).map (algebraMap T C) :=
        Ideal.map_mono hN
    _ = I.map (algebraMap A C) := by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

end SerrePositivity

end PowTorsionPart

section BoundedPowerTorsionQuotientPart

namespace SerrePositivity
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 元の共通 torsion 指数の核で割った商では、a が正則に作用する。 -/
theorem isSMulRegular_quotient_pow_kernel (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0) :
    IsSMulRegular (M ⧸ (a ^ N • (LinearMap.id : M →ₗ[R] M)).ker) a := by
  let T := (a ^ N • (LinearMap.id : M →ₗ[R] M)).ker
  change Function.Injective (a • (LinearMap.id : (M ⧸ T) →ₗ[R] (M ⧸ T)))
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  obtain ⟨x, rfl⟩ := T.mkQ_surjective y
  apply (Submodule.Quotient.mk_eq_zero T).mpr
  have hx : a • x ∈ T := by
    apply (Submodule.Quotient.mk_eq_zero T).mp
    change T.mkQ (a • x) = 0
    rw [map_smul]
    exact hy
  have hx' : a ^ (N + 1) • x = 0 := by
    change a ^ N • (a • x) = 0 at hx
    simpa only [pow_succ, mul_smul] using hx
  exact h (N + 1) x hx'

/-- 有界な a 冪 torsion は、a^N で消える実核と a 正則な実商へ分解できる。 -/
theorem bounded_power_torsion_decomposition (a : R)
    (h : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0) :
    ∃ N : ℕ,
      (∀ x : (a ^ N • (LinearMap.id : M →ₗ[R] M)).ker, a ^ N • x = 0) ∧
      IsSMulRegular (M ⧸ (a ^ N • (LinearMap.id : M →ₗ[R] M)).ker) a := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun x => Subtype.ext x.property,
    isSMulRegular_quotient_pow_kernel a N hN⟩

end SerrePositivity

end BoundedPowerTorsionQuotientPart

section FlatPowerTorsionPart

namespace SerrePositivity
open scoped TensorProduct
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A scalar killing the kernel of multiplication by `a` on the ring also kills
the corresponding kernel on every flat module. -/
theorem smul_eq_zero_of_flat_of_mul_kernel [Module.Flat R M] (a b : R)
    (h : ∀ r : R, a * r = 0 → b * r = 0) (x : M) (hx : a • x = 0) :
    b • x = 0 := by
  let f : R →ₗ[R] R := a • LinearMap.id
  let K := f.ker
  have he : Function.Exact K.subtype f := f.exact_subtype_ker_map
  have ht := Module.Flat.rTensor_exact (M := M) he
  have hz : f.rTensor M ((1 : R) ⊗ₜ[R] x) = 0 := by
    simpa [f, TensorProduct.smul_tmul'] using congrArg (fun y : M ↦ (1 : R) ⊗ₜ[R] y) hx
  obtain ⟨z, hz⟩ := (ht ((1 : R) ⊗ₜ[R] x)).mp hz
  have hk : ∀ z : K ⊗[R] M, b • (TensorProduct.lid R M) (K.subtype.rTensor M z) = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r y =>
      have hrf : f (r : R) = 0 := r.property
      have hr : b * (r : R) = 0 := h r hrf
      simp [smul_smul, hr]
    | add z w hz hw => simp only [map_add, smul_add, hz, hw, add_zero]
  simpa only [hz, TensorProduct.lid_tmul, one_smul] using hk z

/-- Flat modules inherit the same bound on power torsion as the coefficient ring. -/
theorem flat_power_torsion_bound [Module.Flat R M] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) :
    ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0 :=
  fun n x hx ↦ smul_eq_zero_of_flat_of_mul_kernel (a ^ n) (a ^ N) (h n) x hx

/-- A scalar sending a ring kernel into a principal ideal sends the kernel on
a flat module into the corresponding scalar image. -/
theorem smul_eq_smul_of_flat_of_mul_kernel [Module.Flat R M] (a b c : R)
    (h : ∀ r : R, a * r = 0 → ∃ s : R, b * r = c * s)
    (x : M) (hx : a • x = 0) : ∃ y : M, b • x = c • y := by
  let f : R →ₗ[R] R := a • LinearMap.id
  let K := f.ker
  have he : Function.Exact K.subtype f := f.exact_subtype_ker_map
  have ht := Module.Flat.rTensor_exact (M := M) he
  have hz : f.rTensor M ((1 : R) ⊗ₜ[R] x) = 0 := by
    simpa [f, TensorProduct.smul_tmul'] using congrArg (fun y : M ↦ (1 : R) ⊗ₜ[R] y) hx
  obtain ⟨z, hz⟩ := (ht ((1 : R) ⊗ₜ[R] x)).mp hz
  have hk : ∀ z : K ⊗[R] M,
      ∃ y : M, b • (TensorProduct.lid R M) (K.subtype.rTensor M z) = c • y := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r y =>
      obtain ⟨s, hs⟩ := h r (show f (r : R) = 0 from r.property)
      refine ⟨s • y, ?_⟩
      simpa [smul_smul] using congrArg (fun q : R ↦ q • y) hs
    | add z w hz hw =>
      obtain ⟨y, hy⟩ := hz
      obtain ⟨v, hv⟩ := hw
      exact ⟨y + v, by simp only [map_add, smul_add, hy, hv]⟩
  simpa only [hz, TensorProduct.lid_tmul, one_smul] using hk z

end SerrePositivity

end FlatPowerTorsionPart

section FlatPowerQuotientTorsionPart

namespace SerrePositivity
variable {R : Type*} [CommRing R] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
include h

/-- In the `(j+m)`-th quotient, the kernel of `a^m` maps into `(a^j)`
under multiplication by the original ring torsion bound. -/
theorem powerQuotient_mul_kernel_relation (j m : ℕ)
    (x : R ⧸ Ideal.span {a ^ (j + m)})
    (hx : (Ideal.Quotient.mk _ a) ^ m * x = 0) :
    ∃ y : R ⧸ Ideal.span {a ^ (j + m)},
      (Ideal.Quotient.mk _ a) ^ N * x = (Ideal.Quotient.mk _ a) ^ j * y := by
  let I : Ideal R := Ideal.span {a ^ (j + m)}
  let q := Ideal.Quotient.mk I
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hr : a ^ m * r ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp (by
    simpa only [map_mul, map_pow] using hx)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hr
  have he : a ^ m * (r - a ^ j * s) = 0 := by
    rw [mul_sub, ← mul_assoc, ← pow_add, add_comm m j, ← hs, sub_self]
  have hb := h m _ he
  have hb' : a ^ N * r = a ^ j * (a ^ N * s) := by
    rw [mul_sub] at hb
    exact (sub_eq_zero.mp hb).trans (by ring)
  refine ⟨q (a ^ N * s), ?_⟩
  simpa only [map_mul, map_pow] using congrArg q hb'

/-- Flatness over the actual power quotient transfers the ring relation to
arbitrary coefficient modules, with no finite generation assumption. -/
theorem flat_powerQuotient_torsion_relation (j m : ℕ) (M : Type*)
    [AddCommGroup M] [Module (R ⧸ Ideal.span {a ^ (j + m)}) M]
    [Module.Flat (R ⧸ Ideal.span {a ^ (j + m)}) M]
    (x : M) (hx : (Ideal.Quotient.mk (Ideal.span {a ^ (j + m)}) a) ^ m • x = 0) :
    ∃ y : M, (Ideal.Quotient.mk (Ideal.span {a ^ (j + m)}) a) ^ N • x =
      (Ideal.Quotient.mk (Ideal.span {a ^ (j + m)}) a) ^ j • y :=
  smul_eq_smul_of_flat_of_mul_kernel _ _ _
    (fun r hr ↦ powerQuotient_mul_kernel_relation a N h j m r hr) x hx

end SerrePositivity

end FlatPowerQuotientTorsionPart
