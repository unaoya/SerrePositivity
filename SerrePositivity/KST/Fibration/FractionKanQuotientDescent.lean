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
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の同じ coslice 図式を、小さい全充満像を通して元の Verdier 商上へ降下する。 -/
def fractionKanQuotientDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj C.obj ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  spaceDiagramLocalizationDescend q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.quotient
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram q.hom x) (fractionKanSpaceDiagram_inverts_weak h x)

/-- 商関手による制限は、元の底上の同じ coslice 図式と全関手圏内で自然同型。 -/
def fractionKanQuotientDiagram_restrictionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ fractionKanQuotientDiagram h x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram q.hom x) :=
  spaceDiagramLocalizationDescendIso q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.quotient
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram q.hom x) (fractionKanSpaceDiagram_inverts_weak h x)

/-- 元の全単体圏への制限は、元の strict Kan coslice 図式を自然同型で回収する。 -/
def fractionKanQuotientDiagram_simplexIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj ≫ q.hom) ≫
        fractionKanQuotientDiagram h x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x)) := by
  have e := (fractionKanQuotientDiagram_restrictionIso h x).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj))
  rw [← Category.assoc, ← Functor.map_comp] at e
  exact e ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso q.hom x

end SerrePositivity.KST.Fibration
