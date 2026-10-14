module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-! # イデアル進加群の代数的分離性と T2 性

加群のイデアル進位相の基底を用い、冪との積の共通部分が零である条件を移す。
環自身や有限加群に制限しない。
-/

@[expose] public section
namespace SerrePositivity
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

end SerrePositivity
