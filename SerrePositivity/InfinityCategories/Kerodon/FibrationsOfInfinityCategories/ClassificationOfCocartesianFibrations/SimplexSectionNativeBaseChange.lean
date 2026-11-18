module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCoefficientValues
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionBaseChangeValue
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedRealizationValueHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoTransposeEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoCurryComposition

/-!
概要：元の単体切断の底変換係数を、同じ指定比較の通常の自然変換の実現として読む。
方針：元の二変数交換の係数評価を戻し、同じ定義域等式で移した自然変換と照合する。
規約：HTT §3.3.2・Kerodon §5.6（Tag 028T）の構成の特殊な照合。
  全図式の射の類を保ち、単体ごとの像の一致だけで結論しない。
使われ方：P3-C1PNC、残る底変換の長方形を元の自然変換の等式に戻す。
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
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance simplexNative_left {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) := ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 元の定義域の底変換等式を同じ対象で評価した、通常の図式の等式。 -/
lemma simplexSectionNativeTarget_eq {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D ⋙ Over.map k)).evaluate
      (leftFibrationObjectOf p) = transportSimplexFunctor k ⋙
        (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p) := by
  rw [← transportSimplexDomainFunctor_baseChange k, ← relativeSectionEnrichedDiagram_reindex]
  rfl

/-- 元の底変換の共同比較の同じ成分を、指定定義域等式で移した自然変換。 -/
def simplexSectionNativeBaseChange {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
        (leftFibrationObjectOf (pullback.snd p k)) ⋙ kanObjectForget ⟶
      (transportSimplexFunctor k ⋙
        (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p)) ⋙ kanObjectForget :=
  Eq.mp (congrArg (fun T =>
    (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
      (leftFibrationObjectOf (pullback.snd p k)) ⋙ kanObjectForget ⟶ T ⋙ kanObjectForget)
    (simplexSectionNativeTarget_eq p k))
    ((relativeSectionBaseChangeComparison k (transportSimplexDomainFunctor D)).app
      (leftFibrationObjectOf p))

private lemma cast_heq.{v} {A B : Sort v} (h : A = B) (a : A) : HEq (Eq.mp h a) a := by
  cases h
  rfl

private lemma mpr_heq.{v} {A B : Sort v} (h : B = A) (a : A) :
    HEq (Eq.mpr h a) a := by
  cases h
  rfl

private lemma native_hom_heq {J : Type u} [Category.{u} J] {F G F' G' : J ⥤ KanObject.{u}}
    (hF : F = F') (hG : G = G') (η : F ⋙ kanObjectForget ⟶ G ⋙ kanObjectForget)
    (η' : F' ⋙ kanObjectForget ⟶ G' ⋙ kanObjectForget) (hη : HEq η η') :
    HEq (Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
      (F := ⟨F, trivial⟩) (G := ⟨G, trivial⟩) η).toTruncated)
      (Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨F', trivial⟩) (G := ⟨G', trivial⟩) η').toTruncated) := by
  subst F' G'
  cases eq_of_heq hη
  rfl

private lemma baseFamily_heq {B D : SSet.{u}} {J : Type u} [Category.{u} J]
    (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) :
    HEq (relativeSectionDiagramInfinityBaseChangeIso k A)
      (relativeSectionBaseChangeRealizationIso k A).transpose := by
  unfold relativeSectionDiagramInfinityBaseChangeIso
  dsimp only [_root_.id]
  exact cast_heq _ _

private lemma simplexFamily_heq {B D : SSet.{u}} (k : D ⟶ B) :
    HEq (transportSimplexSectionInfinity_baseChangeIso k)
      (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D)) := by
  unfold transportSimplexSectionInfinity_baseChangeIso
  unfold transportSimplexSectionInfinity
  refine (mpr_heq _ _).trans ?_
  exact mpr_heq _ _

private lemma coefficient_value_heq {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq (simplexSectionBaseChangeCoefficient p k)
      (functorIsoValue (relativeSectionBaseChangeRealizationIso k (transportSimplexDomainFunctor D))
        (leftFibrationInfinityVertex p)) := by
  let A := transportSimplexDomainFunctor D
  let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
  have hg : relativeSectionDiagramInfinity (A ⋙ Over.map k) =
      (SSet.uliftFunctor.{u+1,u}).map (nerveMap (transportSimplexFunctor k)) ≫
        transportSimplexSectionInfinity B := by
    rw [transportSimplexSectionInfinity_reindex, transportSimplexDomainFunctor_baseChange]
  have h₁ := functorIso_postcomp_heq_of_heq (relativeSectionDiagramInfinityBaseChangeIso k A)
    (transportSimplexSectionInfinity_baseChangeIso k) rfl hg (simplexFamily_heq k) evp
  have hf : transposeFunctorFamily
      (leftFibrationInfinityBaseChange k ≫ (relativeSectionEnrichedDiagram A).realization) =
      relativeSectionDiagramInfinity A ≫ (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u} :=
    transposeFunctorFamily_comp _ _
  have h₂ := functorIso_postcomp_heq_of_heq (relativeSectionBaseChangeRealizationIso k A).transpose
    (relativeSectionDiagramInfinityBaseChangeIso k A) hf rfl (baseFamily_heq k A) evp
  exact (simplexSectionBaseChangeCoefficient_heq p k).trans
    (h₁.trans (h₂.trans (functorIso_transpose_postcomp_heq_value _ _)))

/-- 元の底変換係数の射の類は、同じ指定比較を移した通常の自然変換の実現とHEq。 -/
@[cite HTT "3.3.2" (partial := special) "全単体切断の指定底変換係数と元の自然変換の実現の照合。"]
lemma simplexSectionBaseChangeCoefficient_native_hom :
    ∀ {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let F : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨(relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
        (leftFibrationObjectOf (pullback.snd p k)), trivial⟩
    let G : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨transportSimplexFunctor k ⋙
        (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p), trivial⟩
    HEq (simplexSectionBaseChangeCoefficient p k).hom
      (Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := F) (G := G) (simplexSectionNativeBaseChange p k)).toTruncated) := by
  intro E B D p hp k
  dsimp only
  let A := transportSimplexDomainFunctor D
  let K := relativeSectionBaseChangeComparison k A
  let hK := relativeSectionBaseChangeComparison_isQCatEquivalence k A
  let H := transportSimplexFunctor k
  have hi : HEq (simplexSectionBaseChangeCoefficient p k)
      (kanEnrichedRealizationValueIso K hK (leftFibrationObjectOf p)) :=
    (coefficient_value_heq p k).trans (relativeSectionBaseChangeValue_heq k A (leftFibrationObjectOf p)).symm
  have ht : kanDiagramCoherentNerve ((relativeSectionEnrichedDiagram (A ⋙ Over.map k)).evaluate
      (leftFibrationObjectOf p)) =
      (SSet.uliftFunctor.{u+1,u}).map (nerveMap H) ≫ simplexSectionValue p :=
    (congrArg (fun T => kanDiagramCoherentNerve T) (simplexSectionNativeTarget_eq p k)).trans
      (kanDiagramCoherentNerve_precomp H _).symm
  have hh := vertexIso_hom_heq rfl (congrArg (fun f => functorVertex f) ht.symm) hi
  rw [kanEnrichedRealizationValueIso_hom] at hh
  have hη : HEq (K.app (leftFibrationObjectOf p)) (simplexSectionNativeBaseChange p k) := by
    unfold simplexSectionNativeBaseChange
    exact (cast_heq _ _).symm
  have hn := native_hom_heq rfl (simplexSectionNativeTarget_eq p k)
    (K.app (leftFibrationObjectOf p)) (simplexSectionNativeBaseChange p k) hη
  exact hh.trans hn

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
