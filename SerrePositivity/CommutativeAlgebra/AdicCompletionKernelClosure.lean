module

public import SerrePositivity.CommutativeAlgebra.AdicModuleMaps
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # 完備化した全射の核と元の核の稠密性

中項が有限生成とは限らない場合も、完備化した全射の核は元の核の像の閉包。
有限生成イデアルの冪商で代表元を取り、全射性で誤差を同じ冪の中で修正する。
完備化した核からの像が閉であることは、この結果だけからは主張しない。
-/

@[expose] public section
namespace SerrePositivity
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

end SerrePositivity
