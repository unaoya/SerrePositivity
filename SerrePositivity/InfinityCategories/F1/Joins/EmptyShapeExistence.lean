module

public import SerrePositivity.InfinityCategories.HomotopyLimits.EmptyCone
public import SerrePositivity.InfinityCategories.Core.InitialOpposite
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LimitColimitOpposite

/-!
概要：終対象・始対象から、任意の表示の空図式の極限・余極限を得る。
方針：空形状間の一意な同型と、空 slice の同型を利用し、余極限は反転する。
規約：指定された元の空図式を保持する。quasicategory 性は要求しない。
使われ方：全有限極限・余極限のセル帰納の空形状基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 終対象から任意の表示の空図式の極限を構成する。 -/
lemma hasLimit_emptyDiagram_of_terminal {T X : SSet.{u}}
    (p : (⊥ : T.Subcomplex).toSSet ⟶ X) (t : X _⦋0⦌) (ht : IsTerminalVertex t) :
    HasLimit p := by
  let e : (⊥ : X.Subcomplex).toSSet ≅ (⊥ : T.Subcomplex).toSSet :=
    Subcomplex.isInitialBot.uniqueUpToIso Subcomplex.isInitialBot
  have he : e.hom ≫ p = (⊥ : X.Subcomplex).ι := Subcomplex.isInitialBot.hom_ext _ _
  apply (F1B.kanHasLimit_iff_restrict_of_isIso p e.hom).mpr
  rw [he]
  exact ⟨HomotopyLimits.emptyCone t, (HomotopyLimits.isLimitCone_emptyCone_iff t).mpr ht⟩

/-- 始対象から任意の表示の空図式の余極限を構成する。 -/
lemma hasColimit_emptyDiagram_of_initial {T X : SSet.{u}}
    (p : (⊥ : T.Subcomplex).toSSet ⟶ X) (t : X _⦋0⦌) (ht : IsInitialVertex t) :
    HasColimit p := by
  apply (F1B.kanHasColimit_iff_hasLimit_op p).mpr
  exact hasLimit_emptyDiagram_of_terminal (T := T.op) (SSet.opFunctor.map p)
    (SSet.opObjEquiv.symm t) ((isInitialVertex_iff_isTerminalVertex_op t).mp ht)

end SerrePositivity.InfinityCategories
