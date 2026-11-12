module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：全自然同型で可換な retract 正方形に沿って、元の関手の同値性を戻す。
方針：大きい比較射の逆を両側の retract と合成し、全自然同型で両逆性を証明する。
規約：元の小さい比較射そのものが同値。写像空間や π₀ の全単射だけに弱めない。
使われ方：普遍錐・余錐の相対始対象性の retract 閉性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 全自然同型で可換な実際の retract 正方形は、元の比較射の同値性を反映する。 -/
lemma isQCatEquivalence_of_retractSquares {A B A' B' : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory A'] [Quasicategory B']
    (f : A ⟶ B) (g : A' ⟶ B') (iA : A ⟶ A') (rA : A' ⟶ A)
    (iB : B ⟶ B') (rB : B' ⟶ B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (iA ≫ rA) (𝟙 A)) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (iB ≫ rB) (𝟙 B))
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ iB) (iA ≫ g))
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ rB) (rA ≫ f)) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  let e := hg.choose
  let v := iB ≫ e.inv ≫ rA
  refine ⟨v, ⟨?_⟩, ⟨?_⟩⟩
  · have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ v) (iA ≫ g ≫ e.inv ≫ rA) := by
      simpa only [v, Category.assoc] using (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp hi (e.inv ≫ rA))
    have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (iA ≫ g ≫ e.inv ≫ rA) (iA ≫ rA) := by
      simpa only [e, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.choose, Category.assoc, Category.comp_id,
        Category.id_comp] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.homInvIso iA) rA)
    exact h₁ ≪≫ h₂ ≪≫ hA
  · have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (v ≫ f) (iB ≫ e.inv ≫ g ≫ rB) := by
      simpa only [v, Category.assoc] using (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp hr.symm (iB ≫ e.inv))
    have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (iB ≫ e.inv ≫ g ≫ rB) (iB ≫ rB) := by
      simpa only [e, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.choose, Category.assoc, Category.comp_id,
        Category.id_comp] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.invHomIso rB) iB)
    exact h₁ ≪≫ h₂ ≪≫ hB

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
