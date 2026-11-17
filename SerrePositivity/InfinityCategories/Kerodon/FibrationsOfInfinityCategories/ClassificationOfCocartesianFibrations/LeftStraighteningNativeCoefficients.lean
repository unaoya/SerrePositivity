module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionBaseChangeValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningFirstVertexTransportValue
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramOppositeValueNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SectionBaseChangeReindex

/-!
概要：既存のunder・底変換・係数反転の指定成分を、同じ通常の図式の値として記録する。
方針：元の共同比較に既存の実現値同型を適用し、指定した三つの成分を合成する。
規約：HTT §3.3.2・Kerodon §5.6（Tag 028T）の指定構成の特殊な成分表示。
  新しい同型を選ばず、既存の成分を同じ対象で評価する略記のみを導入する。
使われ方：P3-C1PNGの指定σの成分表示とP3-C1PNの自然変換の類の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance nativeCoefficients_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 既存のunder前合成の全成分を、元の共同実現に入る同じ比較として記録する。 -/
def nativeUnderJointComparison (B : SSet.{u}) :
    KanEnrichedDiagramComparison
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B))
      (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)) where
  component j := relativeFunctorOverPreComparison
    ((transportSimplexUnderDomainTransformation B).app (Opposite.op j))
  naturality f p := (relativeSectionDiagramComparison (transportSimplexUnderDomainTransformation B) p).naturality f

/-- 元のunder制限比較を同じ対象で評価した指定成分。 -/
def nativeUnderCoefficientIso {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    FunctorIso (simplexSectionValue p)
      (kanDiagramCoherentNerve ((relativeSectionEnrichedDiagram
        (transportSimplexUnderDomains B)).evaluate (leftFibrationObjectOf p))) :=
  kanEnrichedRealizationValueIso (nativeUnderJointComparison B)
    (fun j q => transportSimplexUnderPre_isQCatEquivalence q.val.hom j)
    (leftFibrationObjectOf p)

/-- 元の初頂点底変換比較を同じ対象で評価した指定成分。 -/
def nativeBaseChangeCoefficientIso {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    FunctorIso (leftStraighteningCandidate (pullback.snd p (transportSimplexFirstVertexMap B)))
      (kanDiagramCoherentNerve ((relativeSectionEnrichedDiagram
        (transportSimplexUnderDomains B)).evaluate (leftFibrationObjectOf p))) :=
  kanEnrichedRealizationValueIso
    (relativeSectionBaseChangeComparison (transportSimplexFirstVertexMap B)
      (strictTransportDomains (TransportSimplexCategory B)))
    (relativeSectionBaseChangeComparison_isQCatEquivalence (transportSimplexFirstVertexMap B)
      (strictTransportDomains (TransportSimplexCategory B))) (leftFibrationObjectOf p)

/-- 元の係数反転比較の、同じ左右の成分を評価した指定値。 -/
def nativeOppositeCoefficientIso {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso (leftStraighteningCandidate p) (leftCoherentTransport p) :=
  let D := relativeSectionEnrichedDiagram (strictTransportDomains C)
  let Z := edgewiseOrdinaryObject (leftFibrationObjectOf p)
  (kanEnrichedRealizationValueIso D.edgewiseRightComparison
    (fun j X => isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj X.val).obj)) Z).symm ≪≫
  kanEnrichedRealizationValueIso D.edgewiseLeftComparison
    (fun j X => isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj X.val).obj)) Z

/-- 指定under・初頂点底変換・反転の三成分の同じ合成。 -/
@[cite HTT "3.3.2" (partial := special) "初頂点の相対切断模型の指定係数比較の成分の合成。"]
def firstVertexNativeCoefficientIso {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    FunctorIso (simplexSectionValue p)
      (leftCoherentTransport (pullback.snd p (transportSimplexFirstVertexMap B))) :=
  nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm ≪≫
    nativeOppositeCoefficientIso (pullback.snd p (transportSimplexFirstVertexMap B))

private lemma iso_cast_heq {A B : Sort (u+2)} (h : A = B) (a : A) : HEq (Eq.mp h a) a := by
  cases h
  rfl

/-- 元のunderの指定成分は、元の大域比較の同じ対象での値とHEq。 -/
lemma nativeUnderCoefficientIso_heq {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    HEq (nativeUnderCoefficientIso p)
      (functorIsoValue (transportSimplexUnderRealizationIso B) (leftFibrationInfinityVertex p)) := by
  have h : (nativeUnderJointComparison B).realizationIso
      (fun j q => transportSimplexUnderPre_isQCatEquivalence q.val.hom j) =
      transportSimplexUnderRealizationIso B := by rfl
  have hc : HEq (nativeUnderCoefficientIso p)
      (functorIsoValue ((nativeUnderJointComparison B).realizationIso
        (fun j q => transportSimplexUnderPre_isQCatEquivalence q.val.hom j))
        (leftFibrationInfinityVertex p)) := by
    exact iso_endpoints_heq _ _ _
  exact hc.trans (heq_of_eq (congrArg (fun e => functorIsoValue e (leftFibrationInfinityVertex p)) h))

private lemma underBaseChange_heq (B : SSet.{u}) :
    HEq (transportSimplexUnderBaseChangeRealizationIso B)
      (relativeSectionBaseChangeRealizationIso (transportSimplexFirstVertexMap B)
        (strictTransportDomains (TransportSimplexCategory B))) := by
  unfold transportSimplexUnderBaseChangeRealizationIso
  dsimp only [_root_.id]
  refine (iso_cast_heq _ _).trans ?_
  exact iso_cast_heq _ _

private lemma underBaseChange_source (B : SSet.{u}) :
    leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
        leftStraighteningCoherentMap (TransportSimplexCategory B) =
      leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
        (relativeSectionEnrichedDiagram (strictTransportDomains (TransportSimplexCategory B))).realization := by
  rw [strictTransportDomains_realization]

/-- 元の初頂点底変換の指定成分は、大域比較の同じ対象での値とHEq。 -/
lemma nativeBaseChangeCoefficientIso_heq {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    HEq (nativeBaseChangeCoefficientIso p)
      (functorIsoValue (transportSimplexUnderBaseChangeRealizationIso B)
        (leftFibrationInfinityVertex p)) := by
  let lB := transportSimplexFirstVertexMap B
  let A := strictTransportDomains (TransportSimplexCategory B)
  have hc : HEq (nativeBaseChangeCoefficientIso p)
      (functorIsoValue (relativeSectionBaseChangeRealizationIso lB A) (leftFibrationInfinityVertex p)) :=
    relativeSectionBaseChangeValue_heq lB A (leftFibrationObjectOf p)
  have hv := functorIsoValue_heq_of_heq (transportSimplexUnderBaseChangeRealizationIso B)
    (relativeSectionBaseChangeRealizationIso lB A) (underBaseChange_source B) rfl
    (underBaseChange_heq B) (leftFibrationInfinityVertex p)
  exact hc.trans hv.symm

/-- 元の反転係数の指定成分は、元の反転比較の同じ対象での値とHEq。 -/
lemma nativeOppositeCoefficientIso_heq {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p] :
    HEq (nativeOppositeCoefficientIso p)
      (functorIsoValue (leftStraighteningCoherentMap_oppositeIso C)
        (coherentNerveVertex (edgewiseOrdinaryObject (leftFibrationObjectOf p)))) := by
  let D := relativeSectionEnrichedDiagram (strictTransportDomains C)
  let Z := edgewiseOrdinaryObject (leftFibrationObjectOf p)
  let z := coherentNerveVertex Z
  have h₁ : HEq (leftStraighteningCoherentMap_oppositeIso C) D.oppositeRealizationIso := by
    unfold leftStraighteningCoherentMap_oppositeIso
    dsimp only [_root_.id]
    exact iso_cast_heq _ _
  have hf : edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve C)) ≫ leftStraighteningCoherentMap C =
      edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve C)) ≫ D.realization := by
    rw [strictTransportDomains_realization]
  have hv := functorIsoValue_heq_of_heq (leftStraighteningCoherentMap_oppositeIso C)
    D.oppositeRealizationIso hf rfl h₁ z
  have h := kanEnrichedOppositeValueIso_factor D (leftFibrationObjectOf p)
  have hc : HEq (nativeOppositeCoefficientIso p) (functorIsoValue D.oppositeRealizationIso z) :=
    (heq_of_eq h.symm).trans (iso_endpoints_heq _ _ _)
  exact hc.trans hv.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
