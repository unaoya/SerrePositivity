module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.LaxInitialBoundary
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusionExact
public import SerrePositivity.KST.LocalizingInvariants.RelativeInitialAdjunction

/-!
概要：元の D 包含は第二射影の充満忠実な左随伴である。
方針：第一成分とその像の零性で相対始点境界を充填し、指定単位による随伴判定へ渡す。
規約：随伴を構造体の追加仮定にしない。使われ方：Tamme Prop. 10 の片側の随伴。
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

lemma fromD_fst_vertex (x : D.obj _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p.hom q.hom).app (Opposite.op ⦋0⦌)
      ((fromD p q).app (Opposite.op ⦋0⦌) x) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C.obj).vertex := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (fromD_fst p q)
    (Opposite.op ⦋0⦌)) x
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p.hom q.hom).app (Opposite.op ⦋0⦌)
    ((fromD p q).app (Opposite.op ⦋0⦌) x) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC : D.obj ⟶ C.obj).app _ x at h
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex] using h

lemma fromD_initialBoundary (x : D.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (laxSnd p q).hom ((fromD p q).app (Opposite.op ⦋0⦌) x) := by
  apply lax_snd_initialBoundary p.hom q.hom
  · rw [fromD_fst_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C.obj).isInitial
  · rw [fromD_fst_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := p.hom) _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C.obj).isZero).1

lemma fromD_mapping_equivalence (x : D.obj _⦋0⦌)
    (y : (laxCategory p q).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (laxSnd p q).hom
      ((fromD p q).app (Opposite.op ⦋0⦌) x) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary _ _ _ (fromD_initialBoundary p q x)

/-- 単位は fromD_snd の厳密な恒等から選ぶ、元の両関手の実随伴。 -/
def fromDAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (fromD p q) (laxSnd p q).hom :=
  adjunctionOfRelativeInitialSection (fromD_snd p q) (fromD_initialBoundary p q)

lemma fromDAdjunction_unit : (fromDAdjunction p q).unitHom = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.sectionUnit (fromD_snd p q) :=
  adjunctionOfRelativeInitialSection_unit _ _

lemma fromD_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (fromD p q) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.fullyFaithful_of_relativeInitialSection (fromD_snd p q) (fromD_initialBoundary p q)

end SerrePositivity.KST.LocalizingInvariants.LaxInclusion

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Prop 10"] _root_.SerrePositivity.KST.LocalizingInvariants.LaxInclusion.fromDAdjunction
