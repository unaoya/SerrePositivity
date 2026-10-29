module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # 加群のイデアル進位相

概要：イデアル `I ⊆ R` と `R` 加群 `M` について、`I` 進位相（Mathlib の `Ideal.adicModuleTopology`）の基本性質。
- `I^n M` が零の近傍の基底をなす。
- `M` が `I` 進分離（`IsHausdorff I M`）であることと、位相が T2 であることは同値。
- 線形写像は連続で、分離な加群への線形写像の核は閉。商が分離なら部分加群は閉。
方針：Mathlib の環の場合（`Ideal.hasBasis_nhds_zero_adic`・`IsAdic.isHausdorff_iff`）を加群へ移す。
規約：位相は型クラスではなく `@` で明示的に渡し、型に固定しない。
使われ方：完備化の核の稠密性（`Adic/Completion/Exact`）、冪級数の連続導分。Mathlib への提出候補。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicModuleSeparation

open Topology

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 実際の I 進加群位相の零近傍の基底。 -/
theorem hasBasis_nhds_zero_adicModule (I : Ideal R) :
    Filter.HasBasis (@nhds M (I.adicModuleTopology M) 0) (fun _n : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R M) : Set M)) := by
  let : TopologicalSpace R := I.adicTopology
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  refine ⟨?_⟩
  intro U
  rw [B.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
  change (∃ V : Set M, (∃ n : ℕ, V = ((I ^ n • ⊤ : Submodule R M) : Set M)) ∧ V ⊆ U) ↔ _
  simp

/-- 代数的な I 進分離性は、I 進加群位相の T2 性と同値。 -/
theorem isHausdorff_iff_t2Space_adicModule (I : Ideal R) :
    IsHausdorff I M ↔ @T2Space M (I.adicModuleTopology M) := by
  let : TopologicalSpace R := I.adicTopology
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  rw [B.toAddGroupFilterBasis.t2Space_iff_sInter_subset (t := I.adicModuleTopology M) rfl]
  change IsHausdorff I M ↔
    (⋂₀ {U : Set M | ∃ n : ℕ, U = ((I ^ n • ⊤ : Submodule R M) : Set M)}) ⊆ {0}
  simp [isHausdorff_iff, SModEq.zero, Set.subset_def]

/-- 分離加群について、実際のイデアル進位相の T2 性を供給する。 -/
theorem t2Space_adicModule_of_isHausdorff (I : Ideal R) [IsHausdorff I M] :
    @T2Space M (I.adicModuleTopology M) :=
  (isHausdorff_iff_t2Space_adicModule I).mp inferInstance

end AdicModuleSeparation

section AdicModuleMaps

open Topology

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- 線形写像は同じイデアルによる加群位相について連続。 -/
theorem continuous_linearMap_adic (I : Ideal R) (f : M →ₗ[R] N) :
    @Continuous M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let : WithIdeal R := ⟨I⟩
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := I.adicModuleTopology N
  let : IsTopologicalAddGroup M := by infer_instance
  let : IsTopologicalAddGroup N := by infer_instance
  apply continuous_of_tendsto_nhds_zero f.toAddMonoidHom
  rw [(hasBasis_nhds_zero_adicModule I).tendsto_iff (hasBasis_nhds_zero_adicModule I)]
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro x hx
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) f hx

/-- 分離加群への線形写像の核はイデアル進位相で閉。 -/
theorem isClosed_ker_linearMap_adic (I : Ideal R) [IsHausdorff I N] (f : M →ₗ[R] N) :
    @IsClosed M (I.adicModuleTopology M) (LinearMap.ker f : Set M) := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := I.adicModuleTopology N
  let : T2Space N := t2Space_adicModule_of_isHausdorff I
  exact isClosed_singleton.preimage (continuous_linearMap_adic I f)

/-- 商が分離なら、元の部分加群はイデアル進位相で閉。 -/
theorem isClosed_submodule_adic_of_hausdorff_quotient (I : Ideal R) (P : Submodule R M)
    [IsHausdorff I (M ⧸ P)] : @IsClosed M (I.adicModuleTopology M) (P : Set M) := by
  simpa only [Submodule.ker_mkQ] using isClosed_ker_linearMap_adic I P.mkQ

end AdicModuleMaps

end SerrePositivity
