module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.KST.Fibration.FractionKanInitialInversion
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationUlift
public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization

/-! # 元の coslice 写像空間図式の、同じ底への全関手 ∞ 圏による降下 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory X] [Quasicategory Q] (F : X ⟶ Q) (x : X _⦋0⦌)

/-- 同じ商像の coslice の strict Kan 図式を、元の底上の空間値図式へ降下する。 -/
def fractionKanSpaceDiagram : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  localizationDescend
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdgesLifted X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram F x))
    (fractionSimplexKanMappingDiagram_inverts_initial F x)

/-- 制限は、元の同じ coherent coslice 図式と全関手圏内で自然同型。 -/
def fractionKanSpaceDiagram_restrictionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap X) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram F x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram F x)) :=
  localizationDescendIso
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdgesLifted X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram F x))
    (fractionSimplexKanMappingDiagram_inverts_initial F x)

/-- 降下した図式の初頂点の値は、元の同じ strict Kan coslice 値を表す。 -/
def fractionKanSpaceDiagram_initialVertexIso (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram F x).app (Opposite.op ⦋0⦌)
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram F x).obj c)) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso F x).app (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram F x) c
  exact e ≪≫ eqToIso (congrArg HomotopyCategory.mk hv)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSpaceDiagram := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_initialVertexIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSpaceDiagram_initialVertexIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_initialVertexIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSpaceDiagram_restrictionIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSpaceDiagram_initialVertexIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_initialVertexIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSpaceDiagram_initialVertexIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_initialVertexIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSpaceDiagram_initialVertexIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_initialVertexIso._proof_3
