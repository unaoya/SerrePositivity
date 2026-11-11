module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.PaddedBackwardInsertionComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordBijectiveIso

/-!
# backward 列だけを欠く元の語の単射の padding 比較

概要：像の外が backward 列だけである任意の単射を padding すると graph 写像は弱同値。
方針：元の標的の長さで帰納し、欠けた一列への元の eraseInclusion を因子分解する。
規約：元の写像と全ての列の色を保持し、空語も含む。
使われ方：元の forwardInclusion の padding 比較の全成分。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma paddedBackwardEmbedding_isWeakHomotopyEquivalence {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom)
    (hb : ∀ j, j ∉ Set.range f.orderHom → b.direction j = .backward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map f)) := by
  suffices ∀ n (b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word), b.length = n → ∀ (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (f : a ⟶ b),
      Function.Injective f.orderHom →
      (∀ j, j ∉ Set.range f.orderHom → b.direction j = .backward) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map f)) by
    exact this b.length b rfl a f hf hb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hlen a f hf hb
    by_cases hs : Function.Surjective f.orderHom
    · have : IsIso f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isIso_of_bijective f ⟨hf, hs⟩
      exact _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
    · change ¬ ∀ j, ∃ i, f.orderHom i = j at hs
      obtain ⟨j, hj⟩ := not_forall.mp hs
      let e := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion b j
      have he : Function.Injective e.orderHom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective b j
      let g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding e he f (by
        intro k hk
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_range]
        intro hkj
        exact hj (hkj ▸ hk))
      have hfac (i : Fin a.length) : e.orderHom (g.val.orderHom i) = f.orderHom i :=
        congrArg (fun k => k.orderHom i) g.property
      have hg : Function.Injective g.val.orderHom := by
        intro i k hik
        apply hf
        exact (hfac i).symm.trans ((congrArg e.orderHom hik).trans (hfac k))
      have hgb : ∀ k, k ∉ Set.range g.val.orderHom → (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase b j).direction k = .backward := by
        intro k hk
        have hno : e.orderHom k ∉ Set.range f.orderHom := by
          rintro ⟨i, hi⟩
          exact hk ⟨i, he ((hfac i).trans hi)⟩
        exact (e.direction_eq k).symm.trans (hb _ hno)
      have hlt : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase b j).length < n := by
        rw [← hlen]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase_length_lt b j
      have hgweak := ih _ hlt (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase b j) rfl a g.val hg hgb
      have heweak := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.paddedBackwardInsertion_isWeakHomotopyEquivalence X Y cof b j (hb j hj)
      have hc := hgweak.comp heweak
      rw [← Functor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map_comp, g.property] at hc
      exact hc

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
