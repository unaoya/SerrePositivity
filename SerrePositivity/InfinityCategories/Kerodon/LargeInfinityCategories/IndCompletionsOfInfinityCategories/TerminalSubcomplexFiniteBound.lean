module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalSubcomplexRealization

/-!
概要：有限個の元の添字と有限図式の像は、一つの小さい終頂点付き部分複体に収まる。
方針：像と指定部分複体の有限和を作り、証明済みの終頂点付き拡大を適用する。
規約：同じ部分複体と図式の像を保つ。上界だけで cofinal 性は主張しない。
使われ方：coslice の有限図式を共通の終頂点へ延長する。

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

/-- 有限な両因子の join は有限。 -/
lemma finite_join_of_finite (K L : SSet.{u}) [K.Finite] [L.Finite] : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L).Finite :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_aleph0_iff _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_join Cardinal.isRegular_aleph0
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_aleph0_iff K).mpr inferInstance)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_aleph0_iff L).mpr inferInstance))

/-- 有限個の指定部分複体と元の有限図式の像を同時に含む同じ族内の上界。 -/
lemma exists_terminalSubcomplex_finite_bound {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T) {ι : Type u} [Finite ι]
    (A : ι → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexPredicate _))
    {L : SSet.{u}} [L.Finite] (H : L ⟶ C ⊗ nerve (Codiscrete T)) :
    ∃ B : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexPredicate _),
      (∀ i, A i ≤ B) ∧ Subcomplex.range H ≤ B.val := by
  let M : Option ι → (C ⊗ nerve (Codiscrete T)).Subcomplex
    | none => Subcomplex.range H
    | some i => (A i).val
  have hidx : Cardinal.mk (Option ι) < κ := lt_of_lt_of_le
    (Cardinal.mk_lt_aleph0_iff.mpr inferInstance) hκ.aleph0_le
  have hM : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (M i).toSSet := by
    intro i
    cases i with
    | none => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hκ.aleph0_le _
    | some i => exact (A i).property.1
  have hsmall := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isKappaSmall_iSup_subcomplex hκ hidx M hM
  obtain ⟨B, hB, ht, hUB⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_small_terminalSubcomplex hκ hT (⨆ i, M i) hsmall
  refine ⟨⟨B, hB, ht⟩, ?_, ?_⟩
  · intro i
    exact (le_iSup M (some i)).trans hUB
  · exact (le_iSup M none).trans hUB

/-- 有限図式の頂点に現れる同じ添字と、別の有限図式の像を同時に押さえる。 -/
lemma exists_terminalSubcomplex_bound_diagram {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T) {K L : SSet.{u}} [K.Finite] [L.Finite]
    (a : K ⟶ nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexPredicate _)))
    (H : L ⟶ C ⊗ nerve (Codiscrete T)) :
    ∃ B : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexPredicate _),
      (∀ v : K _⦋0⦌, (a.app _ v).obj 0 ≤ B) ∧ Subcomplex.range H ≤ B.val :=
  exists_terminalSubcomplex_finite_bound hκ hT (fun v : K _⦋0⦌ => (a.app _ v).obj 0) H

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
