module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.WithTopology

/-!
概要：qcqs スキームの準コンパクト開の閉包の点を、その開の点の特殊化として選ぶ。
方針：構成可能位相でのコンパクト性と、準コンパクト開近傍の有限交叉性を使う。
規約：Rydh Proposition 3.7 の閉包の部分。Noether 性は不要。構成可能位相は Stacks 0901。
使われ方：v 被覆の特殊化の持ち上げで、閉包が平坦射の像に入ることを示す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u

/-- 準コンパクト開の閉包の各点は、元の開のある点の特殊化。 -/
theorem exists_specialization_from_compactOpen_closure
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (U : Y.Opens) (hU : IsCompact (U : Set Y)) {y : Y}
    (hy : y ∈ closure (U : Set Y)) : ∃ x : Y, x ∈ U ∧ x ⤳ y := by
  classical
  let P := WithConstructibleTopology Y
  let ofP : P → Y := WithTopology.ofTopology
  have hclosed (V : Y.Opens) (hV : IsCompact (V : Set Y)) :
      IsClosed (ofP ⁻¹' (V : Set Y)) := by
    rw [WithConstructibleTopology.isClosed_iff]
    simpa only [ofP, Set.preimage_preimage, Function.comp_def, WithTopology.ofTopology_toTopology, Set.preimage_id'] using
      hV.isClosed_constructibleTopology_of_isOpen V.isOpen
  let B := {V : Y.Opens // IsCompact (V : Set Y) ∧ y ∈ V}
  let F (V : B) : Set P := ofP ⁻¹' (V.1 : Set Y)
  have hFclosed (V : B) : IsClosed (F V) := hclosed V.1 V.2.1
  have hfinite : ∀ t : Finset B, ((ofP ⁻¹' (U : Set Y)) ∩ ⋂ V ∈ t, F V).Nonempty := by
    intro t
    let O : Y.Opens := ⨅ V : t, V.1.1
    have hyO : y ∈ O := by
      change y ∈ ((⨅ V : t, V.1.1 : Y.Opens) : Set Y)
      simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      exact fun V ↦ V.1.2.2
    obtain ⟨z, hzO, hzU⟩ := mem_closure_iff.mp hy O O.isOpen hyO
    refine ⟨WithTopology.toTopology (constructibleTopology Y) z, hzU, ?_⟩
    apply Set.mem_iInter₂.mpr
    intro V hV
    change z ∈ V.1
    have hz : z ∈ (O : Set Y) := hzO
    rw [TopologicalSpace.Opens.coe_iInf] at hz
    exact Set.mem_iInter.mp hz ⟨V, hV⟩
  obtain ⟨z, hzU, hzF⟩ := (hclosed U hU).isCompact.inter_iInter_nonempty F hFclosed hfinite
  refine ⟨ofP z, hzU, ?_⟩
  by_contra hnot
  obtain ⟨O, hO, hyO, hzO⟩ := not_specializes_iff_exists_open.mp hnot
  obtain ⟨V, ⟨hVo, hVc⟩, hyV, hVO⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyO hO
  exact hzO (hVO (Set.mem_iInter.mp hzF ⟨⟨V, hVo⟩, hVc, hyV⟩))

end SerrePositivity.AlgebraicGeometry
