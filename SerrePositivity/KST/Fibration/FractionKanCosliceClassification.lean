module
public import SerrePositivity.KST.Fibration.LeftCocartesianClassificationPoint
public import SerrePositivity.KST.Fibration.ScaffoldCandidateClassification
public import SerrePositivity.KST.Fibration.FractionKanQuotientDescent
public import SerrePositivity.KST.Fibration.SpaceLocalizationPreFaithful
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningBaseChange

/-! # 同じ商上の coslice 図式を、元の射影の実分類図式と同定する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の全単体圏上の strict Kan 値を、同じ section 比較と表現で分類図式へ送る。 -/
def fractionKanSimplexClassificationIso {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (F : X ⟶ Q) (x : X _⦋0⦌) :
    FunctorIso (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram F x))
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map F ≫ leftStraighteningInfinityDiagram
          (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x))))) := by
  let p := sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x))
  let k := transportSimplexFirstVertexMap X ≫ F
  have e := leftCocartesianKanClassificationIso (pullback.snd p k) ≪≫
    (leftStraighteningInfinityDiagram_baseChangeIso p k).symm
  simpa only [k, p, Functor.map_comp, Category.assoc, cocartesianKanCoherentDiagram,
    fractionSimplexKanMappingDiagram, fractionSimplexCosliceProjection] using e

/-- 初頂点への制限で指定した分類同型。元の section 比較・表現・底変換を保持する。 -/
def fractionKanSpaceDiagram_classificationRestrictionIso {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (F : X ⟶ Q) (x : X _⦋0⦌) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X) ≫
        fractionKanSpaceDiagram F x)
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map F ≫ leftStraighteningInfinityDiagram
          (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x))))) :=
  fractionKanSpaceDiagram_restrictionIso F x ≪≫ fractionKanSimplexClassificationIso F x

/-- 元の底への降下は、同じ商像の coslice 射影の分類図式の制限と自然同型。 -/
def fractionKanSpaceDiagram_classificationIso {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (F : X ⟶ Q) (x : X _⦋0⦌) :
    FunctorIso (fractionKanSpaceDiagram F x)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))) :=
  (localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} X)
    SpaceInfinity.{u}).preimageVertexIso (fractionKanSpaceDiagram_classificationRestrictionIso F x)

/-- 元の Verdier 商へ降ろした図式は、その同じ coslice の実際の分類図式と自然同型。 -/
def fractionKanQuotientDiagram_classificationIso
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) :
    FunctorIso (fractionKanQuotientDiagram h x)
      (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  (spaceLocalizationPre_fullyFaithful q.hom (weakEquivalences i) h.quotient).preimageVertexIso
    (fractionKanQuotientDiagram_restrictionIso h x ≪≫
      fractionKanSpaceDiagram_classificationIso q.hom x)

end SerrePositivity.KST.Fibration
