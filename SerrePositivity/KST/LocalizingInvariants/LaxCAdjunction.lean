module


public meta import SerrePositivity.Util.Citation
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxInclusion

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma fromC_snd_vertex (x : C.obj _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p.hom q.hom).app (Opposite.op ⦋0⦌)
      ((fromC p q).app (Opposite.op ⦋0⦌) x) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex D.obj).vertex := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (fromC_snd p q)
    (Opposite.op ⦋0⦌)) x
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p.hom q.hom).app (Opposite.op ⦋0⦌)
    ((fromC p q).app (Opposite.op ⦋0⦌) x) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD : C.obj ⟶ D.obj).app _ x at h
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex] using h

lemma fromC_terminalBoundary (x : C.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (laxFst p q).hom ((fromC p q).app (Opposite.op ⦋0⦌) x) := by
  apply lax_fst_terminalBoundary p.hom q.hom
  · rw [fromC_snd_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex D.obj).isTerminal
  · rw [fromC_snd_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q.hom) _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex D.obj).isZero).2

def fromCAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (laxFst p q).hom (fromC p q) :=
  adjunctionOfRelativeTerminalSection (fromC_fst p q) (fromC_terminalBoundary p q)

lemma fromC_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (fromC p q) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.fullyFaithful_of_relativeTerminalSection (fromC_fst p q) (fromC_terminalBoundary p q)

instance fromCAdjunction_counit_isIso : IsIso (fromCAdjunction p q).counit :=
  relativeTerminalSection_counit_isIso (fromC_fst p q) (fromC_terminalBoundary p q)

end SerrePositivity.KST.LocalizingInvariants.LaxInclusion

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Prop 10"] _root_.SerrePositivity.KST.LocalizingInvariants.LaxInclusion.fromCAdjunction
