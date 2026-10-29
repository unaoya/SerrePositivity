module

public import Mathlib.RingTheory.AdicCompletion.Exactness
public import SerrePositivity.CommutativeAlgebra.Adic.Topology
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # イデアル進完備化の完全性

概要：
- 一様なフィルトレーションの比較（Artin–Rees 型の評価）があれば、完備化は短完全列・単射を保つ。
  有限加群なら Artin–Rees の補題からその評価が出る。
- 全射 `M → N` の完備化の核は、元の核の像の閉包。完備化の中項が有限なら、完備化した列は完全。
方針：Mathlib の `AdicCompletion.map_exact` は Noether 環と有限加群を仮定するが、ここでは一様な評価だけを使う。
核の閉包は、各冪商での近似を積み上げる（`Adic/Topology` の位相）。
規約：位相は `Ideal.adicModuleTopology` を明示的に渡す。
使われ方：完備微分の推移列（`CompletedDifferential`）、完備性の移行（`Adic/Complete`）。Mathlib への提出候補。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicCompletionInjective

open LinearMap

/-- 誘導フィルトレーションが一様なずれで元のフィルトレーションに含まれるなら、
完備化した写像は単射。有限性・Noether 性は比較の供給側にのみ必要となる。 -/
theorem adicCompletion_map_injective_of_uniform_filtration_bound
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (f : M →ₗ[R] N)
    (hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • (⊤ : Submodule R N)) ≤
        I ^ n • (⊤ : Submodule R M)) :
    Function.Injective (AdicCompletion.map I f) := by
  obtain ⟨k, hk⟩ := hbound
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x (fun a ↦ ?_)
  intro hx
  refine AdicCompletion.mk_zero_of _ _ _ ⟨0, fun n _ ↦ ⟨n + k, by omega, n, by omega, ?_⟩⟩
  apply hk n
  simpa using congrArg (fun x ↦ x.val (n + k)) hx

/-- 有限な終域をもつ単射には Artin–Rees による一様な比較がある。
比較そのものを公開し、完備化の単射性とは独立に再利用できるようにする。 -/
theorem exists_uniform_filtration_bound_of_finite
    {R M N : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Injective f) :
    ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • (⊤ : Submodule R N)) ≤
        I ^ n • (⊤ : Submodule R M) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (range f)
  refine ⟨k, fun n ↦ ?_⟩
  intro x hx
  rw [← Submodule.comap_map_eq_of_injective hf (I ^ n • ⊤ : Submodule R M),
    Submodule.map_smul'', Submodule.map_top]
  apply (smul_mono_right _ inf_le_right :
    I ^ n • (I ^ k • ⊤ ⊓ range f) ≤ _) (show f x ∈ _ from ?_)
  nth_rw 1 [show n = n + k - k by omega]
  rw [← hk (n + k) (show n + k ≥ k by omega)]
  exact ⟨hx, ⟨x, rfl⟩⟩

end AdicCompletionInjective

section AdicCompletionKernelClosure

open Topology

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- 完備化した全射の核の元は、任意の冪を法として元の核の元で近似できる。 -/
theorem exists_ker_approximation_adicCompletion (I : Ideal R) (hI : I.FG)
    (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (x : AdicCompletion I M) (hxg : AdicCompletion.map I g x = 0) (n : ℕ) :
    ∃ a : M, g a = 0 ∧
      x - AdicCompletion.of I M a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
  obtain ⟨a, ha⟩ := (I ^ n • (⊤ : Submodule R M)).mkQ_surjective
    (AdicCompletion.eval I M n x)
  have hx : x - AdicCompletion.of I M a ∈
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub,
      AdicCompletion.eval_of]
    exact sub_eq_zero.mpr ha.symm
  let l := (AdicCompletion.map I g).restrictScalars R
  have hy := Submodule.smul_top_le_comap_smul_top (I ^ n) l hx
  change l (x - AdicCompletion.of I M a) ∈
    I ^ n • (⊤ : Submodule R (AdicCompletion I N)) at hy
  change AdicCompletion.map I g (x - AdicCompletion.of I M a) ∈ _ at hy
  rw [map_sub, hxg, AdicCompletion.map_of, zero_sub] at hy
  have hga : g a ∈ I ^ n • (⊤ : Submodule R N) := by
    have hh := (I ^ n • (⊤ : Submodule R (AdicCompletion I N))).neg_mem hy
    simp only [neg_neg] at hh
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker,
      AdicCompletion.eval_of] at hh
    exact (Submodule.Quotient.mk_eq_zero _).mp hh
  have him : (I ^ n • (⊤ : Submodule R M)).map g = I ^ n • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
  rw [← him] at hga
  obtain ⟨z, hz, hgz⟩ := hga
  refine ⟨a - z, by rw [map_sub, hgz, sub_self], ?_⟩
  have hz' := Submodule.smul_top_le_comap_smul_top (I ^ n) (AdicCompletion.of I M) hz
  convert Submodule.add_mem (I ^ n • (⊤ : Submodule R (AdicCompletion I M))) hx hz' using 1
  rw [map_sub]
  abel

/-- 元の核の像の閉包は、完備化した写像の核に等しい。加群の有限性は不要。 -/
theorem closure_ker_image_eq_ker_adicCompletion_map (I : Ideal R) (hI : I.FG)
    (g : M →ₗ[R] N) (hg : Function.Surjective g) :
    @closure (AdicCompletion I M) (I.adicModuleTopology (AdicCompletion I M))
      (((LinearMap.ker g).map (AdicCompletion.of I M)) : Set (AdicCompletion I M)) =
        (LinearMap.ker ((AdicCompletion.map I g).restrictScalars R) :
          Set (AdicCompletion I M)) := by
  let : WithIdeal R := ⟨I⟩
  let : TopologicalSpace (AdicCompletion I M) := I.adicModuleTopology (AdicCompletion I M)
  let : IsTopologicalAddGroup (AdicCompletion I M) := by infer_instance
  let : IsAdicComplete I (AdicCompletion I N) := AdicCompletion.isAdicComplete hI
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨a, ha, rfl⟩
      change AdicCompletion.map I g (AdicCompletion.of I M a) = 0
      rw [AdicCompletion.map_of, LinearMap.mem_ker.mp ha, map_zero]
    · exact isClosed_ker_linearMap_adic I ((AdicCompletion.map I g).restrictScalars R)
  · intro x hx
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    obtain ⟨n, _, hn⟩ :=
      (hasBasis_nhds_zero_adicModule (M := AdicCompletion I M) I).mem_iff.mp hU
    obtain ⟨a, ha, hxa⟩ := exists_ker_approximation_adicCompletion I hI g hg x hx n
    refine ⟨AdicCompletion.of I M a, ⟨a, ha, rfl⟩, hn ?_⟩
    change AdicCompletion.of I M a - x ∈
      I ^ n • (⊤ : Submodule R (AdicCompletion I M))
    simpa only [neg_sub] using
      (I ^ n • (⊤ : Submodule R (AdicCompletion I M))).neg_mem hxa

/-- 右完全列を完備化すると、最初の写像の像の閉包が次の写像の核になる。
最初の写像の単射性・加群の有限性・Noether性は不要。 -/
theorem closure_range_adicCompletion_map_eq_ker
    {P : Type*} [AddCommGroup P] [Module R P]
    (I : Ideal R) (hI : I.FG) (f : P →ₗ[R] M) (g : M →ₗ[R] N)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    @closure (AdicCompletion I M) (I.adicModuleTopology (AdicCompletion I M))
      (LinearMap.range ((AdicCompletion.map I f).restrictScalars R) :
        Set (AdicCompletion I M)) =
          (LinearMap.ker ((AdicCompletion.map I g).restrictScalars R) :
            Set (AdicCompletion I M)) := by
  let : TopologicalSpace (AdicCompletion I M) := I.adicModuleTopology (AdicCompletion I M)
  let : IsAdicComplete I (AdicCompletion I N) := AdicCompletion.isAdicComplete hI
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨a, rfl⟩
      change AdicCompletion.map I g (AdicCompletion.map I f a) = 0
      rw [← LinearMap.comp_apply, AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero,
        AdicCompletion.map_zero, LinearMap.zero_apply]
    · exact isClosed_ker_linearMap_adic I ((AdicCompletion.map I g).restrictScalars R)
  · rw [← closure_ker_image_eq_ker_adicCompletion_map I hI g hg]
    apply closure_mono
    rintro _ ⟨a, ha, rfl⟩
    rw [hfg.linearMap_ker_eq] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨AdicCompletion.of I P b, AdicCompletion.map_of I f b⟩

/-- 完備化した中項が有限なら、像の閉包を像自身に戻して完全性を得る。
通常の中項の有限性・最初の写像の単射性は要求しない。 -/
theorem adicCompletion_map_exact_of_finite_completion
    {P : Type*} [AddCommGroup P] [Module R P] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    [Module.Finite R (AdicCompletion I M)]
    (f : P →ₗ[R] M) (g : M →ₗ[R] N)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact ((AdicCompletion.map I f).restrictScalars R)
      ((AdicCompletion.map I g).restrictScalars R) := by
  let F := (AdicCompletion.map I f).restrictScalars R
  let : TopologicalSpace (AdicCompletion I M) := I.adicModuleTopology (AdicCompletion I M)
  let : IsHausdorff I (AdicCompletion I M ⧸ LinearMap.range F) :=
    IsHausdorff.of_le_jacobson I _ hI
  have hc : IsClosed (LinearMap.range F : Set (AdicCompletion I M)) :=
    isClosed_submodule_adic_of_hausdorff_quotient I (LinearMap.range F)
  have he := closure_range_adicCompletion_map_eq_ker I I.fg_of_isNoetherianRing f g hfg hg
  rw [hc.closure_eq] at he
  exact Set.ext_iff.mp he.symm

end AdicCompletionKernelClosure

section AdicCompletionExact

open LinearMap Submodule AdicCompletion

/-- 一様なフィルトレーション比較と右全射性があれば、完備化は完全性を保つ。
加群の有限性・環の Noether 性は要求せず、比較条件の供給側に分離する。 -/
theorem adicCompletion_map_exact_of_uniform_filtration_bound
    {R M N P : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (I : Ideal R)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • (⊤ : Submodule R N)) ≤
        I ^ n • (⊤ : Submodule R M)) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  obtain ⟨k, hk⟩ := hbound
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun y ↦ ?_)
  · rw [AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · apply AdicCompletion.induction_on I N y (fun b ↦ ?_)
    intro hz
    have hb (n : ℕ) : g (b n) ∈ (I ^ n • ⊤ : Submodule R P) := by
      simpa using congrArg (fun x ↦ x.val n) hz
    have hlift (n : ℕ) : ∃ a : M,
        f a - b (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N) := by
      have hmem : g (b (k + n)) ∈ Submodule.map g
          (I ^ (k + n) • ⊤ : Submodule R N) := by
        rw [map_smul'', Submodule.map_top, range_eq_top.mpr hg]
        exact hb (k + n)
      obtain ⟨d, hdmem, hd⟩ := hmem
      obtain ⟨a, ha⟩ := (hfg (b (k + n) - d)).mp (by simp [hd])
      exact ⟨a, by simpa [ha] using (I ^ (k + n) • (⊤ : Submodule R N)).neg_mem hdmem⟩
    choose a ha using hlift
    have hstep (n : ℕ) : a (n + 1) - a n ∈ (I ^ n • ⊤ : Submodule R M) := by
      apply hk n
      change f (a (n + 1) - a n) ∈ (I ^ (n + k) • (⊤ : Submodule R N))
      have hle : (I ^ (k + (n + 1)) • ⊤ : Submodule R N) ≤
          I ^ (k + n) • ⊤ :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
      have hdelta : b (k + (n + 1)) - b (k + n) ∈
          (I ^ (k + n) • ⊤ : Submodule R N) := by
        rw [← Submodule.Quotient.eq]
        exact AdicCauchySequence.mk_eq_mk (by omega) b
      have hsum := (I ^ (k + n) • (⊤ : Submodule R N)).sub_mem
        ((I ^ (k + n) • (⊤ : Submodule R N)).add_mem (hle (ha (n + 1))) hdelta) (ha n)
      convert hsum using 1 <;> simp [map_sub, Nat.add_comm]
    refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M a ?_), ?_⟩
    · intro n
      apply SModEq.symm
      simpa only [SModEq.sub_mem] using hstep n
    · ext n
      suffices he : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f (a n)) =
          Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (b (k + n)) by
        simp [he, AdicCauchySequence.mk_eq_mk (show n ≤ k + n by omega)]
      rw [Submodule.Quotient.eq]
      exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (show n ≤ k + n by omega))) (ha n)

end AdicCompletionExact

end SerrePositivity
