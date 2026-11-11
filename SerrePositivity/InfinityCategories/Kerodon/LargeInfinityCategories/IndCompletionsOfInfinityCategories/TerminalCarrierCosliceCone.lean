module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalSubcomplexCarrier
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalSubcomplexCosliceCone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrierConeLift
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.NestedCosliceCoconeValue

/-!
概要：元の値写像の上で一致する有限 coslice 図式は、同じ実現空間内の余錐へ延びる。
方針：共通の指定終頂点への二つの余錐を、既存の二重 coslice 比較と同じ実現空間で貼る。
規約：元の両図式への制限と値写像上での一致を厳密に保持する。
使われ方：値写像の coslice 引き戻しの filtered 性と cofinal 性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の二図式に一致し、同じ値写像の上で一致する二つの余錐が存在する。 -/
lemma exists_terminalCarrier_cosliceCone {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T) {K : SSet.{u}} [K.Finite]
    (p : (Δ[0] : SSet.{u}) ⟶ C ⊗ nerve (Codiscrete T))
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrier κ (C ⊗ nerve (Codiscrete T)))
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierValue κ _ = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) :
    ∃ (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f),
      c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierValue κ _ = d.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  let X := C ⊗ nerve (Codiscrete T)
  obtain ⟨B, cI, hB, hI, cB, hcB⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_terminalSubcomplex_cosliceCone hκ hT
    (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierProjection κ _) p f
  let cX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f) := ⟨cB.val ≫ B.val.ι, by
    rw [← Category.assoc, cB.property, Subcomplex.lift_ι]⟩
  have hcX : cX.vertex = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexChosenVertex κ X B).val := by
    change B.val.ι.app _ cB.vertex = _
    rw [hcB]
    rfl
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.diagramNestedCosliceDiagramCurry f Δ[0] cX
  let F := d.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ F = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierValue κ X := by
    rw [← Category.assoc, d.property]
    exact h.symm
  have hbound : Subcomplex.range F ≤ B.val := by
    have hb := Subfunctor.range_comp_le cB.val B.val.ι
    rw [Subfunctor.range_ι] at hb
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nestedCosliceCocone_value_range_le f cX).trans hb
  have hFapex : F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K) = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexChosenVertex κ X B).val := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p).app _ (d.val.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K)) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.joinCocone_vertex_eq_map_apex d]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nestedCosliceCocone_vertex f cX).trans hcX
  have hIapex : cI.val.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.joinCocone_vertex_eq_map_apex cI).symm.trans hI
  obtain ⟨G, hG, hvalue, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_terminalCarrier_cone_lift
    (fun A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ X (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexPredicate X) => A.val)
    (fun A => (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexChosenVertex κ X A).val)
    a F cI.val B hF cI.property hbound hFapex hIapex
  exact ⟨⟨G, hG⟩, d, hvalue⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
