module

public import SerrePositivity.AlgebraicGeometry.FiniteAffineCover
public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCover

/-!
概要：元の切断の逆像開被覆を有限アフィン被覆で細分する。
方針：各点でアフィン開を選び、準コンパクト性で有限部分被覆を取る。
規約：元の被覆への添字写像を保持し、一つの開に収まる仮定を加えない。
使われ方：切断に適合する局所のČech計算（承認済み計画F01）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の切断の逆像開被覆に適合する有限アフィン細分が存在する。 -/
theorem exists_section_adapted_affine_cover
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of R) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : ι → Y.Opens) (hcU : (⨆ i, U i) = ⊤) :
    ∃ (n : ℕ) (V : Fin n → (Spec (CommRingCat.of R)).Opens) (ρ : Fin n → ι),
      (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = ⊤ ∧
        ∀ j, V j ≤ s ⁻¹ᵁ U (ρ j) := by
  classical
  have hc := s.iSup_preimage_eq_top hcU
  have hloc (x : Spec (CommRingCat.of R)) :
      ∃ (i : ι) (W : (Spec (CommRingCat.of R)).Opens),
        IsAffineOpen W ∧ x ∈ W ∧ W ≤ s ⁻¹ᵁ U i := by
    have hx : x ∈ ⨆ i, s ⁻¹ᵁ U i := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨W, hW, hxW, hWi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨i, W, hW, hxW, hWi⟩
  choose ρ V hV hxV hle using hloc
  obtain ⟨a, ha⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (V x : Set (Spec (CommRingCat.of R)))) (fun x ↦ (V x).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  let e := (Fintype.equivFin ↥a).symm
  refine ⟨Fintype.card ↥a, (fun j ↦ V (e j)), (fun j ↦ ρ (e j)),
    (fun j ↦ hV _), ?_, (fun j ↦ hle _)⟩
  apply le_antisymm le_top
  intro x _
  obtain ⟨y, hya, hxy⟩ := Set.mem_iUnion₂.mp (ha (Set.mem_univ x))
  refine Opens.mem_iSup.mpr ⟨(Fintype.equivFin ↥a) ⟨y, hya⟩, ?_⟩
  simpa only [e, Equiv.symm_apply_apply, SetLike.mem_coe] using hxy

end SerrePositivity.AlgebraicGeometry
