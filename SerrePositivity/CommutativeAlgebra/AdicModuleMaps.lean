module

public import SerrePositivity.CommutativeAlgebra.AdicModuleSeparation
public import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # イデアル進加群の線形写像と閉部分加群

線形写像の連続性と、商の分離性から得られる部分加群の閉性。
環のNoether性・加群の有限生成性は、この一般層には不要。
-/

@[expose] public section
namespace SerrePositivity
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

end SerrePositivity
