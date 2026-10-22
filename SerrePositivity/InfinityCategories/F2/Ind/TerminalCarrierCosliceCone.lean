module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalSubcomplexCarrier
public import SerrePositivity.InfinityCategories.F2.Ind.TerminalSubcomplexCosliceCone
public import SerrePositivity.InfinityCategories.F2.Ind.TerminalCarrierConeLift
public import SerrePositivity.InfinityCategories.F2.Ind.NestedCosliceCoconeValue

/-!
概要：元の値写像の上で一致する有限 coslice 図式は、同じ実現空間内の余錐へ延びる。
方針：共通の指定終頂点への二つの余錐を、既存の二重 coslice 比較と同じ実現空間で貼る。
規約：元の両図式への制限と値写像上での一致を厳密に保持する。
使われ方：値写像の coslice 引き戻しの filtered 性と cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の二図式に一致し、同じ値写像の上で一致する二つの余錐が存在する。 -/
lemma exists_terminalCarrier_cosliceCone {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T) {K : SSet.{u}} [K.Finite]
    (p : (Δ[0] : SSet.{u}) ⟶ C ⊗ nerve (Codiscrete T))
    (a : K ⟶ terminalSubcomplexCarrier κ (C ⊗ nerve (Codiscrete T)))
    (f : K ⟶ sliceUnder p)
    (h : a ≫ terminalSubcomplexCarrierValue κ _ = f ≫ sliceUnderProjection p) :
    ∃ (c : JoinCocone a) (d : JoinCocone f),
      c.val ≫ terminalSubcomplexCarrierValue κ _ = d.val ≫ sliceUnderProjection p := by
  let X := C ⊗ nerve (Codiscrete T)
  obtain ⟨B, cI, hB, hI, cB, hcB⟩ := exists_terminalSubcomplex_cosliceCone hκ hT
    (a ≫ terminalSubcomplexCarrierProjection κ _) p f
  let cX : JoinCocone (sliceUnderUncurry f) := ⟨cB.val ≫ B.val.ι, by
    rw [← Category.assoc, cB.property, Subcomplex.lift_ι]⟩
  have hcX : cX.vertex = (terminalSubcomplexChosenVertex κ X B).val := by
    change B.val.ι.app _ cB.vertex = _
    rw [hcB]
    rfl
  let d : JoinCocone f := diagramNestedCosliceDiagramCurry f Δ[0] cX
  let F := d.val ≫ sliceUnderProjection p
  have hF : joinInl K Δ[0] ≫ F = a ≫ terminalSubcomplexCarrierValue κ X := by
    rw [← Category.assoc, d.property]
    exact h.symm
  have hbound : Subcomplex.range F ≤ B.val := by
    have hb := Subfunctor.range_comp_le cB.val B.val.ι
    rw [Subfunctor.range_ι] at hb
    exact (nestedCosliceCocone_value_range_le f cX).trans hb
  have hFapex : F.app _ (coneApex K) = (terminalSubcomplexChosenVertex κ X B).val := by
    change (sliceUnderProjection p).app _ (d.val.app _ (coneApex K)) = _
    rw [← joinCocone_vertex_eq_map_apex d]
    exact (nestedCosliceCocone_vertex f cX).trans hcX
  have hIapex : cI.val.app _ (coneApex K) = nerveVertex B :=
    (joinCocone_vertex_eq_map_apex cI).symm.trans hI
  obtain ⟨G, hG, hvalue, _⟩ := exists_terminalCarrier_cone_lift
    (fun A : SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X) => A.val)
    (fun A => (terminalSubcomplexChosenVertex κ X A).val)
    a F cI.val B hF cI.property hbound hFapex hIapex
  exact ⟨⟨G, hG⟩, d, hvalue⟩

end SerrePositivity.InfinityCategories.F2.Ind
