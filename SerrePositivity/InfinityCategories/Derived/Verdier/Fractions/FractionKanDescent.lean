module
public import SerrePositivity.KST.Fibration.FractionKanInitialInversion
public import SerrePositivity.InfinityCategories.F1.Transport.LocalizationUlift
public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization

/-! # 元の coslice 写像空間図式の、同じ底への全関手 ∞ 圏による降下 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory X] [Quasicategory Q] (F : X ⟶ Q) (x : X _⦋0⦌)

/-- 同じ商像の coslice の strict Kan 図式を、元の底上の空間値図式へ降下する。 -/
def fractionKanSpaceDiagram : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ SpaceInfinity.{u} :=
  localizationDescend
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X))
    (transportSimplexInitialEdgesLifted X) (transportSimplexFirstVertexMap_ulift_isLocalization X)
    (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram F x))
    (fractionSimplexKanMappingDiagram_inverts_initial F x)

/-- 制限は、元の同じ coherent coslice 図式と全関手圏内で自然同型。 -/
def fractionKanSpaceDiagram_restrictionIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X) ≫
        fractionKanSpaceDiagram F x)
      (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram F x)) :=
  localizationDescendIso
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X))
    (transportSimplexInitialEdgesLifted X) (transportSimplexFirstVertexMap_ulift_isLocalization X)
    (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram F x))
    (fractionSimplexKanMappingDiagram_inverts_initial F x)

/-- 降下した図式の初頂点の値は、元の同じ strict Kan coslice 値を表す。 -/
def fractionKanSpaceDiagram_initialVertexIso (c : TransportSimplexCategory X) :
    VertexIso ((fractionKanSpaceDiagram F x).app (Opposite.op ⦋0⦌)
      (ULift.up ((transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (nerveVertex c))))
      (spaceInfinityVertex ((fractionSimplexKanMappingDiagram F x).obj c)) := by
  have e := (fractionKanSpaceDiagram_restrictionIso F x).app (ULift.up (nerveVertex c))
  have hv := kanDiagramCoherentNerve_vertex (fractionSimplexKanMappingDiagram F x) c
  exact e ≪≫ eqToIso (congrArg HomotopyCategory.mk hv)

end SerrePositivity.KST.Fibration
