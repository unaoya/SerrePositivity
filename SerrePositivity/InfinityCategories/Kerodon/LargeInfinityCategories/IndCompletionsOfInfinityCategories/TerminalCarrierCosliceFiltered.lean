module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrierCosliceCone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CodiscreteProductCofinal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InnerPullback
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility

/-!
概要：全鎖の実現空間の値写像の各 coslice 引き戻しは filtered。
方針：元の二成分の有限余錐を同じ値写像の上で貼り、通常の引き戻し内の余錐にする。
規約：ラベルの非空性は指定した元の点から回収し、追加仮定にしない。
使われ方：Quillen A による同じ値写像の cofinal 性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

instance terminalCarrierCoslice_quasicategory (κ : Cardinal.{u}) (C : SSet.{u})
    [Quasicategory C] (T : Type u) (p : (Δ[0] : SSet.{u}) ⟶ C ⊗ nerve (Codiscrete T)) :
    Quasicategory (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierValue κ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)) := by
  have : Nonempty T := ⟨(nerveEquiv
    ((snd C (nerve (Codiscrete T))).app _ (SSet.yonedaEquiv p))).as⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.quasicategory_pullback_of_innerFibration_right _ _

/-- 同じ coslice 引き戻しの全ての有限図式は、元の図式を延長する余錐を持つ。 -/
lemma terminalCarrierCoslice_isFiltered {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T)
    (p : (Δ[0] : SSet.{u}) ⟶ C ⊗ nerve (Codiscrete T)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity
      (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierValue κ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)) := by
  constructor
  intro K _ f
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierValue κ (C ⊗ nerve (Codiscrete T))
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p
  have h : (f ≫ pullback.fst v r) ≫ v = (f ≫ pullback.snd v r) ≫ r := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  obtain ⟨c, d, hcd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_terminalCarrier_cosliceCone hκ hT p
    (f ≫ pullback.fst v r) (f ≫ pullback.snd v r) h
  refine ⟨⟨pullback.lift c.val d.val hcd, ?_⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact c.property
  · rw [Category.assoc, pullback.lift_snd]
    exact d.property

/-- 同じ coslice 引き戻しは弱可縮。 -/
lemma terminalCarrierCoslice_isWeaklyContractible {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T)
    (p : (Δ[0] : SSet.{u}) ⟶ C ⊗ nerve (Codiscrete T)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible
      (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierValue κ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)) := by
  have := terminalCarrierCoslice_isFiltered hκ hT p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
