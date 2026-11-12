module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.EmptyCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite

/-!
概要：終対象・始対象から、任意の表示の空図式の極限・余極限を得る。
方針：空形状間の一意な同型と、空 slice の同型を利用し、余極限は反転する。
規約：指定された元の空図式を保持する。quasicategory 性は要求しない。
使われ方：全有限極限・余極限のセル帰納の空形状基底。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 終対象から任意の表示の空図式の極限を構成する。 -/
lemma hasLimit_emptyDiagram_of_terminal {T X : SSet.{u}}
    (p : (⊥ : T.Subcomplex).toSSet ⟶ X) (t : X _⦋0⦌) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p := by
  let e : (⊥ : X.Subcomplex).toSSet ≅ (⊥ : T.Subcomplex).toSSet :=
    Subcomplex.isInitialBot.uniqueUpToIso Subcomplex.isInitialBot
  have he : e.hom ≫ p = (⊥ : X.Subcomplex).ι := Subcomplex.isInitialBot.hom_ext _ _
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasLimit_iff_restrict_of_isIso p e.hom).mpr
  rw [he]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.emptyCone t, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_emptyCone_iff t).mpr ht⟩

/-- 始対象から任意の表示の空図式の余極限を構成する。 -/
lemma hasColimit_emptyDiagram_of_initial {T X : SSet.{u}}
    (p : (⊥ : T.Subcomplex).toSSet ⟶ X) (t : X _⦋0⦌) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_hasLimit_op p).mpr
  exact hasLimit_emptyDiagram_of_terminal (T := T.op) (SSet.opFunctor.map p)
    (SSet.opObjEquiv.symm t) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_isTerminalVertex_op t).mp ht)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
