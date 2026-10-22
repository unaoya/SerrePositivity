module
public import SerrePositivity.KST.Fibration.FractionKanWeakInversion
public import SerrePositivity.KST.Fibration.SpaceDiagramLocalizationDescent

/-! # 商の coslice を表す同じ空間値図式の、元の Verdier 商への降下 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の同じ coslice 図式を、小さい全充満像を通して元の Verdier 商上へ降下する。 -/
def fractionKanQuotientDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj C.obj ⟶ SpaceInfinity.{u} :=
  spaceDiagramLocalizationDescend q.hom (weakEquivalences i) h.quotient
    (fractionKanSpaceDiagram q.hom x) (fractionKanSpaceDiagram_inverts_weak h x)

/-- 商関手による制限は、元の底上の同じ coslice 図式と全関手圏内で自然同型。 -/
def fractionKanQuotientDiagram_restrictionIso :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ fractionKanQuotientDiagram h x)
      (fractionKanSpaceDiagram q.hom x) :=
  spaceDiagramLocalizationDescendIso q.hom (weakEquivalences i) h.quotient
    (fractionKanSpaceDiagram q.hom x) (fractionKanSpaceDiagram_inverts_weak h x)

/-- 元の全単体圏への制限は、元の strict Kan coslice 図式を自然同型で回収する。 -/
def fractionKanQuotientDiagram_simplexIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj ≫ q.hom) ≫
        fractionKanQuotientDiagram h x)
      (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram q.hom x)) := by
  have e := (fractionKanQuotientDiagram_restrictionIso h x).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj))
  rw [← Category.assoc, ← Functor.map_comp] at e
  exact e ≪≫ fractionKanSpaceDiagram_restrictionIso q.hom x

end SerrePositivity.KST.Fibration
