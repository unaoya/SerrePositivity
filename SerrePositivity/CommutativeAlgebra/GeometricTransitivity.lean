module

public import SerrePositivity.CommutativeAlgebra.GeometricFiber
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# 不変元から幾何ファイバーでの推移性（論文 §5.1 のノルムの議論）

## 概要

有限群 `G` が `A` 代数 `T` に `A` 線形に作用し、`G` で固定される元はすべて `A` から来る
（`T^G = A`）とする。`T` が `A` 上有限なら、`G` はすべての幾何ファイバー `Spec(T ⊗_A Ω)` に推移的に
作用する（`isGeometricallyTransitive_of_fixed`）。

## 方針（論文 §5.1）

不変元の環が係数拡大と可換であることは使わない。

1. **ノルムはスカラー**（`exists_prod_tensorAction_eq`）：`u = Σ t_i ⊗ ω_i` について
   `Π_g g(u)` は `Ω` の像に入る。多項式 `Π_g Σ_i g(t_i) X_i` は `G` で不変なので係数は `A` に入り、
   `X_i = ω_i` で特殊化すればよい。
2. `S = T ⊗_A Ω` は `Ω` 上有限なので Artin 環で、`Spec S` は離散。`x` の軌道 `O` に対し
   `basicOpen e = O` となる冪等元 `e` をとる。`f = Π_g g(e)` も冪等元で、`O` が `G` で安定なので
   `basicOpen f = O`。一方 `f` はスカラーで冪等なので `0` か `1`。`x ∈ O` から `f = 1`、`O = Spec S`。
-/

@[expose] public section

universe u

open TensorProduct

namespace SerrePositivity

variable (A T G : Type u) [CommRing A] [CommRing T] [Algebra A T] [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T]

section action

variable (Ω : Type u) [CommRing Ω] [Algebra A Ω]

lemma tensorAction_tmul (g : G) (t : T) (ω : Ω) :
    tensorAction A T G Ω g (t ⊗ₜ ω) = (g • t) ⊗ₜ ω := rfl

lemma tensorAction_mul (g h : G) (z : T ⊗[A] Ω) :
    tensorAction A T G Ω (g * h) z = tensorAction A T G Ω g (tensorAction A T G Ω h z) := by
  induction z using TensorProduct.inductionOn with
  | tmul t ω => simp only [tensorAction_tmul, mul_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma tensorAction_one (z : T ⊗[A] Ω) : tensorAction A T G Ω 1 z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul t ω => simp only [tensorAction_tmul, one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {A T G}

/-- **ノルムはスカラー**：`T^G = A` なら、`u ∈ T ⊗_A Ω` について `Π_g g(u)` は `Ω` の像に入る。 -/
theorem exists_prod_tensorAction_eq [Fintype G]
    (hfix : ∀ t : T, (∀ g : G, g • t = t) → t ∈ Set.range (algebraMap A T))
    (u : T ⊗[A] Ω) :
    ∃ c : Ω, ∏ g, tensorAction A T G Ω g u = Algebra.TensorProduct.includeRight c := by
  classical
  obtain ⟨F, rfl⟩ := TensorProduct.exists_finset u
  let P : MvPolynomial F T :=
    ∏ g : G, ∑ i : F, MvPolynomial.C (g • i.1.1) * MvPolynomial.X i
  -- `P` は `G` 不変
  have hP : ∀ g : G, MvPolynomial.map (MulSemiringAction.toRingHom G T g) P = P := by
    intro g
    simp only [P, map_prod, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      MulSemiringAction.toRingHom_apply, ← mul_smul]
    exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ (fun _ ↦ rfl)
  -- 係数は `A` から来る
  have hc : (P.coeffs : Set T) ⊆ Set.range (algebraMap A T) := by
    intro c hcP
    obtain ⟨d, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hcP
    refine hfix _ fun g ↦ ?_
    have := congrArg (fun q : MvPolynomial F T ↦ q.coeff d) (hP g)
    rwa [MvPolynomial.coeff_map] at this
  obtain ⟨Q, hQ⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hc
  -- 特殊化
  let iL := (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] Ω).toRingHom
  let iR := (Algebra.TensorProduct.includeRight : Ω →ₐ[A] T ⊗[A] Ω)
  let ω : F → Ω := fun i ↦ i.1.2
  have h1 : MvPolynomial.eval₂ iL (fun i ↦ iR (ω i)) P =
      ∏ g, tensorAction A T G Ω g (∑ i ∈ F, i.1 ⊗ₜ[A] i.2) := by
    simp only [P, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, map_sum, tensorAction_tmul]
    refine Finset.prod_congr rfl fun g _ ↦ ?_
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change ((g • i.1.1) ⊗ₜ[A] (1 : Ω)) * ((1 : T) ⊗ₜ[A] i.1.2) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h2 : MvPolynomial.eval₂ iL (fun i ↦ iR (ω i)) (MvPolynomial.map (algebraMap A T) Q) =
      iR (MvPolynomial.eval₂ (algebraMap A Ω) ω Q) := by
    rw [MvPolynomial.eval₂_map]
    have hcomp : iL.comp (algebraMap A T) = iR.toRingHom.comp (algebraMap A Ω) :=
      RingHom.ext fun a ↦ by
        simp only [iL, iR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          AlgHom.commutes]
    rw [hcomp]
    exact (MvPolynomial.eval₂_comp_left iR.toRingHom (algebraMap A Ω) ω Q).symm
  exact ⟨_, h1.symm.trans (hQ ▸ h2)⟩

end action

variable {A T G}

/-- `T ⊗_A Ω` は `T` が `A` 上有限なら Artin 環（`Ω` 体）。 -/
lemma isArtinianRing_tensor [Module.Finite A T] (Ω : Type u) [Field Ω] [Algebra A Ω] :
    IsArtinianRing (T ⊗[A] Ω) := by
  have : IsArtinianRing (Ω ⊗[A] T) := IsArtinianRing.of_finite Ω (Ω ⊗[A] T)
  exact (Algebra.TensorProduct.comm A Ω T).toRingEquiv.isArtinianRing

/-- **論文 §5.1 のノルムの議論**：`T` が `A` 上有限で `T^G = A` なら、`G` は `Spec T → Spec A` の
すべての幾何ファイバーに推移的に作用する。

証明：`S = T ⊗_A Ω` は Artin 環なので `Spec S` は離散。`x` の軌道 `O` に `basicOpen e = O` となる
冪等元 `e` をとり、`f = Π_g g(e)` とおく。素イデアル `p` について `f ∉ p` は「すべての `g` で
`g^* p ∈ O`」と同値。`f` は冪等なスカラー（`exists_prod_tensorAction_eq`）なので `0` か `1` で、
`f ∉ x` から `f = 1`。よって `f ∉ y` で、`g = 1` として `y ∈ O`。 -/
theorem isGeometricallyTransitive_of_fixed [Finite G] [Module.Finite A T]
    (hfix : ∀ t : T, (∀ g : G, g • t = t) → t ∈ Set.range (algebraMap A T)) :
    IsGeometricallyTransitive A T G := by
  intro Ω _ _ _ x y
  have := Fintype.ofFinite G
  have := isArtinianRing_tensor (A := A) (T := T) Ω
  let τ : G → T ⊗[A] Ω →+* T ⊗[A] Ω := fun g ↦ (tensorAction A T G Ω g).toRingHom
  let O : Set (PrimeSpectrum (T ⊗[A] Ω)) := Set.range fun g ↦ PrimeSpectrum.comap (τ g) x
  obtain ⟨e, he, hO⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (isClopen_discrete O)
  -- `τ g e ∉ p ↔ g^* p ∈ O`
  have hmem : ∀ (g : G) (p : PrimeSpectrum (T ⊗[A] Ω)),
      τ g e ∉ p.asIdeal ↔ PrimeSpectrum.comap (τ g) p ∈ O := by
    intro g p
    rw [hO, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    rfl
  obtain ⟨c, hc⟩ := exists_prod_tensorAction_eq Ω hfix e
  have hf : ∀ p : PrimeSpectrum (T ⊗[A] Ω), Algebra.TensorProduct.includeRight c ∉ p.asIdeal ↔
      ∀ g : G, PrimeSpectrum.comap (τ g) p ∈ O := by
    intro p
    rw [← hc]
    change (∏ g, τ g e) ∉ p.asIdeal ↔ _
    rw [Ideal.IsPrime.prod_mem_iff]
    simp only [Finset.mem_univ, true_and, not_exists, hmem]
  have hx : Algebra.TensorProduct.includeRight c ∉ x.asIdeal :=
    (hf x).mpr fun g ↦ ⟨g, rfl⟩
  -- `includeRight` は単射（`S` は自明でない）
  have : Nontrivial (T ⊗[A] Ω) := ⟨⟨0, 1, fun h ↦ x.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ x.asIdeal.zero_mem))⟩⟩
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : Ω →ₐ[A] T ⊗[A] Ω) :=
    (Algebra.TensorProduct.includeRight : Ω →ₐ[A] T ⊗[A] Ω).toRingHom.injective
  -- `c` は冪等
  have hcc : c * c = c := by
    apply hinj
    rw [map_mul, ← hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ ↦ ?_
    rw [← map_mul, he.eq]
  have hc1 : c = 1 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcc with h | h
    · exact absurd (by rw [h, map_zero]; exact x.asIdeal.zero_mem) hx
    · exact h
  have hy : Algebra.TensorProduct.includeRight c ∉ y.asIdeal := by
    rw [hc1, map_one]
    exact fun h ↦ y.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  obtain ⟨g, hg⟩ := (hf y).mp hy 1
  refine ⟨g, hg.trans ?_⟩
  ext1
  ext z
  exact (show z ∈ (Ideal.comap (τ 1) y.asIdeal) ↔ z ∈ y.asIdeal by
    rw [Ideal.mem_comap]; change tensorAction A T G Ω 1 z ∈ _ ↔ _; rw [tensorAction_one])

end SerrePositivity
