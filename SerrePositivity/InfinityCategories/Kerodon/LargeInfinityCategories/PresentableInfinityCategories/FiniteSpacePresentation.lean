module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteKanReplacementCompact
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratorEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamilyColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：元の小さい Kan 空間を、有限部分複体の Kan 置換の filtered 全余極限として表示する。
方針：有限部分複体の元の包含余錐に連続 Kan 置換を施し、同じ全余錐を native に実現する。
規約：元の指定頂点へ厳密に戻す。全表示の各項の compact 性を実証する。
使われ方：空間の小さい compact 生成圏と presentable 性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSpacePresentation

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 元の空間の有限部分複体の包含順。 -/
abbrev FiniteSpacePieces (X : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily Cardinal.aleph0 X (fun _ ↦ True)

instance finiteSpacePieces_isFiltered (X : SSet.{u}) : IsFiltered (FiniteSpacePieces X) :=
  isFiltered_of_isCardinalFiltered _ Cardinal.aleph0

instance finiteSpacePiece_finite {X : SSet.{u}} (A : FiniteSpacePieces X) : A.val.toSSet.Finite :=
  ⟨Cardinal.lt_aleph0_iff_finite.mp A.property.1⟩

/-- 元の有限部分複体の nerve は、全 coherent な有限試験図式に対して filtered。 -/
lemma finiteSpacePieces_nerve_isKappaFiltered (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered Cardinal.aleph0 (nerve (FiniteSpacePieces X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _

/-- 元の有限部分複体に同じ連続 Kan 置換を施した全図式。 -/
def finiteSpaceReplacementDiagram (X : SSet.{u}) : FiniteSpacePieces X ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj A := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementKanObject A.val.toSSet
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map f)
  map_id A := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map (𝟙 A)) =
        𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj A.val.toSSet)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map (f ≫ g)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map g)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- 元の包含の Kan 置換を全脚とする、同じ置換空間への余錐。 -/
def finiteSpaceReplacementCocone (X : SSet.{u}) : Cocone (finiteSpaceReplacementDiagram X) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementKanObject X
  ι := {
    app A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map A.val.ι
    naturality A B f := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map f) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map B.val.ι = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map A.val.ι
      rw [← CategoryTheory.Functor.map_comp]
      exact congrArg (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map k)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamilyCocone Cardinal.aleph0 X (fun _ ↦ True)).w f) }

/-- 同じ元の余錐は、忘却後に通常の filtered 余極限である。 -/
def finiteSpaceReplacementCocone_isColimit (X : SSet.{u}) :
    IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone (finiteSpaceReplacementCocone X)) :=
  isColimitOfPreserves _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamilyCocone_isColimit Cardinal.aleph0 X (fun _ ↦ True)
      (fun A hA ↦ ⟨A, hA, trivial, le_rfl⟩))

/-- 同じ有限模型の全余錐は、元の空間 ∞ 圏で native な余極限となる。 -/
lemma finiteSpaceReplacementCocone_native (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (finiteSpaceReplacementCocone X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictNativeCocone_isColimit_of_filtered_forget _
    (finiteSpaceReplacementCocone_isColimit X)

/-- 元の同じ全図式の全項は、N の定義により compact である。 -/
lemma finiteSpaceReplacementDiagram_compact (X : SSet.{u})
    (a : (nerve (FiniteSpacePieces X)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} Cardinal.aleph0
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (finiteSpaceReplacementDiagram X)).app _ (ULift.up a)) := by
  obtain ⟨A, rfl⟩ := nerveEquiv.symm.surjective a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact Cardinal.aleph0
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (finiteSpaceReplacementDiagram X)).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteKanReplacement_isCompact A.val.toSSet

/-- 元の指定 Kan 空間そのものを、同じ有限模型の compact な filtered 全表示で回収する。 -/
lemma exists_finiteSpacePresentation (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (finiteSpaceReplacementDiagram K.obj)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K := by
  let f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementKanObject K.obj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app K.obj
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence K.obj
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := hw.isSimplicialHomotopyEquivalence.isQCatEquivalence
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence hf
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated) := he
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementKanObject K.obj)) :=
    asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated)
  let c := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (finiteSpaceReplacementCocone K.obj)
  have hc := finiteSpaceReplacementCocone_native K.obj
  have hv : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementKanObject K.obj) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_vertex _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_colimitCone_vertex_of_iso c hc
    (eqToIso (congrArg HomotopyCategory.mk hv) ≪≫ e.symm)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSpacePresentation
