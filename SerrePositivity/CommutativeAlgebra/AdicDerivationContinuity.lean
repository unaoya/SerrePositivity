module

public import SerrePositivity.RingTheory.Derivation
public import SerrePositivity.CommutativeAlgebra.AdicModuleSeparation
public import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # 通常の導分のイデアル進連続性

δ(I^(n+1)) ⊆ I^n M の評価を零近傍の基底へ移す。
終域の分離性・完備性は連続性の証明には不要。
-/

@[expose] public section
namespace SerrePositivity
open Topology

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M]

/-- 任意の導分は、源と終域の同じイデアルによる位相で連続。 -/
theorem continuous_derivation_adic (δ : Derivation R S M) (I : Ideal S) :
    @Continuous S M I.adicTopology (I.adicModuleTopology M) δ := by
  let : WithIdeal S := ⟨I⟩
  let : TopologicalSpace M := I.adicModuleTopology M
  let : IsTopologicalAddGroup M := by infer_instance
  apply continuous_of_tendsto_nhds_zero δ.toAddMonoidHom
  rw [I.hasBasis_nhds_zero_adic.tendsto_iff (hasBasis_nhds_zero_adicModule I)]
  intro n _
  refine ⟨n + 1, trivial, ?_⟩
  intro x hx
  exact derivation_mem_pow_smul δ I n hx

end SerrePositivity
