module

public import SerrePositivity.AlgebraicGeometry.CompactOpenSpecialization

/-!
概要：qcqs スキームの構成可能集合を、構成可能位相のコンパクト性で扱う。
方針：構成可能位相で閉かつコンパクトな集合の連続像を取る。
規約：既存の Stacks 0901 の構成可能位相のコンパクト性の法則。
使われ方：有限表示な固有射の像の補開の準コンパクト性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry TopologicalSpace Topology
open scoped Topology
universe u

/-- qcqs スキームの構成可能集合は元の位相で準コンパクト。 -/
theorem isCompact_of_isConstructible_scheme
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {s : Set X} (hs : IsConstructible s) : IsCompact s := by
  let P := WithConstructibleTopology X
  let f : P → X := WithTopology.ofTopology
  have hcont : Continuous f := by
    apply PrespectralSpace.isTopologicalBasis.continuous_iff.mpr
    rintro U ⟨hUo, hUc⟩
    rw [WithConstructibleTopology.isOpen_iff]
    simpa only [f, Set.preimage_preimage, Function.comp_def,
      WithTopology.ofTopology_toTopology, Set.preimage_id'] using
      hUc.isOpen_constructibleTopology_of_isOpen hUo
  have hopen : IsOpen[constructibleTopology X] sᶜ := by
    rw [constructibleTopology_eq_generateFrom_isConstructible]
    exact isOpen_generateFrom_of_mem hs.compl
  have hclosed : IsClosed (f ⁻¹' s) := by
    rw [← isOpen_compl_iff, WithConstructibleTopology.isOpen_iff]
    simpa only [f, ← Set.preimage_compl, Set.preimage_preimage, Function.comp_def,
      WithTopology.ofTopology_toTopology, Set.preimage_id'] using hopen
  have heq : f '' (f ⁻¹' s) = s :=
    Set.image_preimage_eq s (WithTopology.ofTopology_surjective _)
  rw [← heq]
  exact hclosed.isCompact.image hcont

end SerrePositivity.AlgebraicGeometry
