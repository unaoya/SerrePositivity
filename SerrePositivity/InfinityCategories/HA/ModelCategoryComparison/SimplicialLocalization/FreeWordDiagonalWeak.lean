module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnForwardStep
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnBackwardStep
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnMixedStep
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnReverseStep
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalEmptyWeak

/-!
# 元の全語の自由対角 augmentation の弱同値性

概要：任意の向き付き語で元の左比較射自身が弱同値となる。
方針：空語・一列の基底と、元の四つの先頭方向の帰納段階を長さ帰納で結ぶ。
規約：元の全対象・全語・全単体作用素と同じ augmentation を保持する。
使われ方：DK5.7の元の全語の余極限への移送。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SerrePositivity.EInfinity.Hammock _root_.SerrePositivity.InfinityCategories
lemma freeWordDiagonalAugmentation_weak (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app w) := by
  have h : ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word, ∀ X Y : C.category,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app a) := by
    intro a
    induction a using _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.induction_on with
    | h0 => exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation_empty_weak C
    | hs d v ih =>
      intro X Y
      cases hv : v.length with
      | zero =>
        have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.eq_empty_of_length_zero v hv
        subst v
        cases d with
        | forward =>
          exact Eq.mpr (congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
            ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons_empty .forward))
              (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation_forward_weak C X Y)
        | backward =>
          exact Eq.mpr (congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
            ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons_empty .backward))
              (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation_backward_weak C X Y)
      | succ n =>
        obtain ⟨e, t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_cons_of_length_succ v n hv
        subst v
        cases d with
        | forward =>
          cases e with
          | forward =>
            exact _root_.SerrePositivity.EInfinity.SimplicialLocalization.freeWordDiagonalAugmentation_cons_forwardForward_weak C t X Y
              (fun Z => ih Z Y)
          | backward =>
            exact _root_.SerrePositivity.EInfinity.SimplicialLocalization.freeWordDiagonalAugmentation_cons_forwardBackward_weak C t X Y
              (fun Z => ih Z Y)
        | backward =>
          cases e with
          | forward =>
            exact _root_.SerrePositivity.EInfinity.SimplicialLocalization.freeWordDiagonalAugmentation_cons_backwardForward_weak C t X Y
              (fun Z => ih Z Y)
          | backward =>
            exact _root_.SerrePositivity.EInfinity.SimplicialLocalization.freeWordDiagonalAugmentation_cons_backwardBackward_weak C t X Y
              (fun Z => ih Z Y)
  exact h w X Y
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
