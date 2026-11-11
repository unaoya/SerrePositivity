module

public import SerrePositivity.KST.Spectra.SpectrumNativeCotensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulIso

/-!
概要：native cotensor の完全忠実性を、元の普遍評価の全 Hom の後合成の同値性へ還元する。
方針：元の整合写像の二射影の可換条件と、既存の自明 Kan fibration を消去する。
規約：条件を結論として仮定しない。使われ方：円の native loop の実際の Hom 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance cotensorFaithfulnessSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance cotensorFaithfulnessHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
local instance cotensorFaithfulnessEvaluationKan (A : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) :
    KanComplex ((CategoryTheory.ihom A).obj
      (RawSpectrumMapping.pointedSpace (cotensor A X) Y.toKanSequence)).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
namespace CotensorCompatible

/-- 元の cotensor の Hom 射影が同値であることを、同じ全 Hom の評価後合成で検出する。 -/
lemma cotensorMap_isQCatEquivalence_iff (A : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cotensorMap A X Y).right ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (evaluationPost A X Y).right := by
  let preTrivial :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (cotensorEvaluationPrecomposition (cotensor A X) Y A).right :=
    cotensorEvaluationPrecomposition_trivialKanFibration (cotensor A X) Y A
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (cotensorEvaluationPrecomposition (cotensor A X) Y A).right :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
      (cotensorEvaluationPrecomposition (cotensor A X) Y A).right).isQCatEquivalence
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (sourceMap A X Y).right :=
    (sourceEquivalence A X Y).isQCatEquivalence
  have hc := congrArg Under.Hom.right (condition A X Y)
  simp only [Under.comp_right] at hc
  constructor
  · intro h
    apply hs.cancel_left
    rw [← hc]
    exact h.comp hp
  · intro h
    apply hp.cancel_right
    rw [hc]
    exact hs.comp h

/-- 元の cotensor 射影の coherent nerve の完全忠実性は、全 Hom の評価後合成で判定。 -/
lemma cotensorInfinityMap_isFullyFaithful_iff (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (cotensorInfinityMap A) ↔
      ∀ X Y : OmegaSpectrum.{u}, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (evaluationPost A X Y).right := by
  constructor
  · intro h X Y
    exact (cotensorMap_isQCatEquivalence_iff A X Y).1
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff (cotensorEnriched A)).1 h ⟨X⟩ ⟨Y⟩)
  · intro h
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff (cotensorEnriched A)).2
    intro X Y
    exact (cotensorMap_isQCatEquivalence_iff A X.val Y.val).2 (h X.val Y.val)

end CotensorCompatible

/-- 元の native cotensor の完全忠実性を、元の BF 普遍評価の全写像空間の同値性へ戻す。 -/
lemma nativeCotensor_isFullyFaithful_iff (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (nativeCotensor A) ↔
      ∀ X Y : OmegaSpectrum.{u},
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (CotensorCompatible.evaluationPost A X Y).right := by
  constructor
  · intro h
    apply (CotensorCompatible.cotensorInfinityMap_isFullyFaithful_iff A).1
    apply (nativeCotensor_sourceIso A).isFullyFaithful_iff.1
    exact (CotensorCompatible.sourceInfinityMap_isFullyFaithful A).comp h
  · intro h
    have hc := (CotensorCompatible.cotensorInfinityMap_isFullyFaithful_iff A).2 h
    exact (CotensorCompatible.sourceInfinityEquivalence A).symm.isFullyFaithful.comp hc

end SerrePositivity.KST.Spectra.OmegaSpectrum
