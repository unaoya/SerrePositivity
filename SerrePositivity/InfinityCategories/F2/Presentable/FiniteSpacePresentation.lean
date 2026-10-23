module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteKanReplacementCompact
public import SerrePositivity.InfinityCategories.F2.Presentable.GeneratorEquivalence
public import SerrePositivity.InfinityCategories.F2.Ind.SmallSubcomplexFamilyColimit
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible

/-!
概要：元の小さい Kan 空間を、有限部分複体の Kan 置換の filtered 全余極限として表示する。
方針：有限部分複体の元の包含余錐に連続 Kan 置換を施し、同じ全余錐を native に実現する。
規約：元の指定頂点へ厳密に戻す。全表示の各項の compact 性を実証する。
使われ方：空間の小さい compact 生成圏と presentable 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 元の空間の有限部分複体の包含順。 -/
abbrev FiniteSpacePieces (X : SSet.{u}) :=
  Ind.SmallSubcomplexFamily Cardinal.aleph0 X (fun _ ↦ True)

instance finiteSpacePieces_isFiltered (X : SSet.{u}) : IsFiltered (FiniteSpacePieces X) :=
  isFiltered_of_isCardinalFiltered _ Cardinal.aleph0

instance finiteSpacePiece_finite {X : SSet.{u}} (A : FiniteSpacePieces X) : A.val.toSSet.Finite :=
  ⟨Cardinal.lt_aleph0_iff_finite.mp A.property.1⟩

/-- 元の有限部分複体の nerve は、全 coherent な有限試験図式に対して filtered。 -/
lemma finiteSpacePieces_nerve_isKappaFiltered (X : SSet.{u}) :
    IsKappaFiltered Cardinal.aleph0 (nerve (FiniteSpacePieces X)) :=
  Ind.isKappaFiltered_nerve_of_cardinalFiltered _

/-- 元の有限部分複体に同じ連続 Kan 置換を施した全図式。 -/
def finiteSpaceReplacementDiagram (X : SSet.{u}) : FiniteSpacePieces X ⥤ KanObject.{u} where
  obj A := continuousReplacementKanObject A.val.toSSet
  map f := continuousKanReplacement.map
    ((Ind.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map f)
  map_id A := by
    change continuousKanReplacement.map
      ((Ind.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map (𝟙 A)) =
        𝟙 (continuousKanReplacement.obj A.val.toSSet)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    change continuousKanReplacement.map
      ((Ind.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map (f ≫ g)) =
        continuousKanReplacement.map
          ((Ind.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map f) ≫
        continuousKanReplacement.map
          ((Ind.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map g)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- 元の包含の Kan 置換を全脚とする、同じ置換空間への余錐。 -/
def finiteSpaceReplacementCocone (X : SSet.{u}) : Cocone (finiteSpaceReplacementDiagram X) where
  pt := continuousReplacementKanObject X
  ι := {
    app A := continuousKanReplacement.map A.val.ι
    naturality A B f := by
      change continuousKanReplacement.map
        ((Ind.smallSubcomplexFamilyDiagram Cardinal.aleph0 X (fun _ ↦ True)).map f) ≫
          continuousKanReplacement.map B.val.ι = continuousKanReplacement.map A.val.ι
      rw [← CategoryTheory.Functor.map_comp]
      exact congrArg (fun k ↦ continuousKanReplacement.map k)
        ((Ind.smallSubcomplexFamilyCocone Cardinal.aleph0 X (fun _ ↦ True)).w f) }

/-- 同じ元の余錐は、忘却後に通常の filtered 余極限である。 -/
def finiteSpaceReplacementCocone_isColimit (X : SSet.{u}) :
    IsColimit (kanObjectForget.mapCocone (finiteSpaceReplacementCocone X)) :=
  isColimitOfPreserves continuousKanReplacement
    (Ind.smallSubcomplexFamilyCocone_isColimit Cardinal.aleph0 X (fun _ ↦ True)
      (fun A hA ↦ ⟨A, hA, trivial, le_rfl⟩))

/-- 同じ有限模型の全余錐は、元の空間 ∞ 圏で native な余極限となる。 -/
lemma finiteSpaceReplacementCocone_native (X : SSet.{u}) :
    IsColimitCone (strictNativeCocone (finiteSpaceReplacementCocone X)) :=
  Ind.strictNativeCocone_isColimit_of_filtered_forget _
    (finiteSpaceReplacementCocone_isColimit X)

/-- 元の同じ全図式の全項は、N の定義により compact である。 -/
lemma finiteSpaceReplacementDiagram_compact (X : SSet.{u})
    (a : (nerve (FiniteSpacePieces X)) _⦋0⦌) :
    Compact.IsKappaCompact.{u, u + 1} Cardinal.aleph0
      ((strictCoherentDiagram (finiteSpaceReplacementDiagram X)).app _ (ULift.up a)) := by
  obtain ⟨A, rfl⟩ := nerveEquiv.symm.surjective a
  change Compact.IsKappaCompact Cardinal.aleph0
    ((strictCoherentDiagram (finiteSpaceReplacementDiagram X)).app _ (ULift.up (nerveVertex A)))
  rw [strictCoherentDiagram_eq_kanDiagram]
  erw [kanDiagramCoherentNerve_vertex, spaceInfinityVertex_eq_coherent]
  exact finiteKanReplacement_isCompact A.val.toSSet

/-- 元の指定 Kan 空間そのものを、同じ有限模型の compact な filtered 全表示で回収する。 -/
lemma exists_finiteSpacePresentation (K : KanObject.{u}) :
    ∃ d : JoinCocone (strictCoherentDiagram (finiteSpaceReplacementDiagram K.obj)),
      IsColimitCone d ∧ d.vertex = coherentNerveVertex K := by
  let f : K ⟶ continuousReplacementKanObject K.obj := continuousKanReplacementUnit.app K.obj
  have hw : IsWeakHomotopyEquivalence f :=
    continuousKanReplacementUnit_isWeakHomotopyEquivalence K.obj
  have hf : IsQCatEquivalence f := hw.isSimplicialHomotopyEquivalence.isQCatEquivalence
  have he := coherentKanEdge_isInvertible_of_isQCatEquivalence hf
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated) := he
  let e : VertexIso (coherentNerveVertex K)
      (coherentNerveVertex (continuousReplacementKanObject K.obj)) :=
    asIso (SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated)
  let c := strictNativeCocone (finiteSpaceReplacementCocone K.obj)
  have hc := finiteSpaceReplacementCocone_native K.obj
  have hv : c.vertex = coherentNerveVertex (continuousReplacementKanObject K.obj) :=
    strictNativeCocone_vertex _
  exact exists_colimitCone_vertex_of_iso c hc
    (eqToIso (congrArg HomotopyCategory.mk hv) ≪≫ e.symm)

end SerrePositivity.InfinityCategories.F2.Presentable
