module

public import SerrePositivity.KST.LocalizingInvariants.LaxArrowTransformation
public import SerrePositivity.KST.LocalizingInvariants.FullStableExact
public import SerrePositivity.KST.LocalizingInvariants.PullbackDifferenceVertices
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationStability

/-!
概要：通常 pullback は安定 ∞ 圏であり、元の lax pullback への比較包含は完全。
方針：同値矢印の頂点条件の安定閉性と F2 の全部分複体への厳密同型を使う。
規約：元の Cat∞ の pullback と射影を保持する。使われ方：K-8(d) の差の商の左項。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

instance equivalenceSubcomplex_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalenceSubcomplex p.hom q.hom : SSet.{u}) :=
  FullSubcomplex.isStable (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsLaxEquivalenceVertex p.hom q.hom)
    (laxEquivalenceVertex_stable p q)

instance ordinaryPullback_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p.hom q.hom) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso p.hom q.hom
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_trivialKanFibration e.hom

instance pullbackComparison_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax p.hom q.hom) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex_ι]
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso p.hom q.hom).hom :=
    inferInstance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p.hom q.hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsLaxEquivalenceVertex p.hom q.hom)).ι :=
    FullSubcomplex.inclusion_isExact _ (laxEquivalenceVertex_stable p q)
  exact inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso p.hom q.hom).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p.hom q.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsLaxEquivalenceVertex p.hom q.hom)).ι))

/-- F2 の元の通常 pullback を K-5 の安定対象へ束ねる。 -/
def pullbackCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p.hom q.hom, inferInstance, inferInstance⟩

/-- 元の通常 pullback の全単体上の比較包含。 -/
def pullbackInclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (pullbackCategory p q) (laxCategory p q) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax p.hom q.hom, inferInstance⟩

lemma pullbackInclusion_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (pullbackInclusion p q).hom :=
  pullbackComparison_fullyFaithful p q

def pullbackFst : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (pullbackCategory p q) C where
  hom := (pullbackInclusion p q).hom ≫ (laxFst p q).hom
  isExact := inferInstance

def pullbackSnd : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (pullbackCategory p q) D where
  hom := (pullbackInclusion p q).hom ≫ (laxSnd p q).hom
  isExact := inferInstance

lemma pullbackFst_hom : (pullbackFst p q).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p.hom q.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_fst p.hom q.hom

lemma pullbackSnd_hom : (pullbackSnd p q).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p.hom q.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_snd p.hom q.hom

end SerrePositivity.KST.LocalizingInvariants
