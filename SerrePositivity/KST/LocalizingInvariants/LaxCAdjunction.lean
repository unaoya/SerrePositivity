module

public import SerrePositivity.KST.LocalizingInvariants.LaxTerminalBoundary
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusionExact
public import SerrePositivity.KST.LocalizingInvariants.RelativeTerminalAdjunction

/-!
概要：元の C 包含は第一射影の充満忠実な右随伴である。
方針：第二成分とその像の零性で相対終点境界を充填し、反転側の随伴を戻す。
規約：元の関手を保持する。使われ方：Tamme Prop. 10 の右側の随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxInclusion

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma fromC_snd_vertex (x : C.obj _⦋0⦌) :
    (F2.laxPullbackSnd p.hom q.hom).app (Opposite.op ⦋0⦌)
      ((fromC p q).app (Opposite.op ⦋0⦌) x) = (chosenZeroVertex D.obj).vertex := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (fromC_snd p q)
    (Opposite.op ⦋0⦌)) x
  change (F2.laxPullbackSnd p.hom q.hom).app (Opposite.op ⦋0⦌)
    ((fromC p q).app (Opposite.op ⦋0⦌) x) = (zeroD : C.obj ⟶ D.obj).app _ x at h
  simpa only [zeroD, zeroDiagram_const_vertex] using h

lemma fromC_terminalBoundary (x : C.obj _⦋0⦌) :
    TerminalBoundaryLifting (laxFst p q).hom ((fromC p q).app (Opposite.op ⦋0⦌) x) := by
  apply lax_fst_terminalBoundary p.hom q.hom
  · rw [fromC_snd_vertex]
    exact (chosenZeroVertex D.obj).isTerminal
  · rw [fromC_snd_vertex]
    exact (IsExactFunctor.preservesZero (F := q.hom) _ (chosenZeroVertex D.obj).isZero).2

def fromCAdjunction : QCatAdjunction (laxFst p q).hom (fromC p q) :=
  adjunctionOfRelativeTerminalSection (fromC_fst p q) (fromC_terminalBoundary p q)

lemma fromC_fullyFaithful : IsFullyFaithful (fromC p q) :=
  fullyFaithful_of_relativeTerminalSection (fromC_fst p q) (fromC_terminalBoundary p q)

instance fromCAdjunction_counit_isIso : IsIso (fromCAdjunction p q).counit :=
  relativeTerminalSection_counit_isIso (fromC_fst p q) (fromC_terminalBoundary p q)

end SerrePositivity.KST.LocalizingInvariants.LaxInclusion
