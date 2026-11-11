module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalSubcomplexCofinal

/-!
概要：小さい κ-filtered ∞ 圏には、小さい通常の κ-filtered poset からの cofinal map がある。
方針：κ と同じ濃度のラベルを取り、構成済みの小さい終頂点付き部分複体の包含順を使う。
規約：元の ∞ 圏を標的にし、通常の κ-filtered 性と cofinal 性を両方証明する。
使われ方：一般の coherent な前層図式の添字を strict な図式へ移す工程。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 小さい κ-filtered ∞ 圏には、小さい通常の κ-filtered poset による cofinal な添字がある。 -/
lemma exists_cofinal_cardinalFiltered_poset {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C] :
    ∃ (I : Type u) (o : PartialOrder I),
      letI := o
      ∃ f : nerve I ⟶ C, IsCardinalFiltered I κ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f := by
  have hκ : κ.IsRegular := Fact.out
  let T := κ.out
  have hT : κ ≤ Cardinal.mk T := by rw [Cardinal.mk_out]
  let I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexPredicate _)
  refine ⟨I, inferInstance, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexBaseMap κ C T, ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexFamily_isCardinalFiltered hT
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexBaseMap_isRightCofinal hκ hT

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
