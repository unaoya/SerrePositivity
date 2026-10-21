module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentPointTotalProjection
public import SerrePositivity.InfinityCategories.F2.CoherentTotalCocone

/-!
概要：定値終対象 coherent 図式の元の余極限頂点は、sifted な底上で終対象。
方針：元の小さい全空間の射影を Kan 置換し、底の一点比較へ合成する。
規約：頂点は元の coherentDiagramTotalCocone の頂点を使う。
使われ方：sifted な空間値余極限の空積保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 定値一点図式の元の余極限 Kan 模型から一点への比較は、元の射影の像。 -/
def coherentPointTotalTerminalKanMap (B : SSet.{u}) :
    F2.coherentDiagramTotalKanObject
      (SSet.const pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _) ⟶
        pointKanObject.{u} :=
  F2.continuousKanReplacement.map (smallLeftUnstraighteningProjection
    (SSet.const pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _)) ≫
      siftedTerminalKanMap B

/-- 同じ比較は元の全空間の Kan 置換単位と厳密に可換。 -/
lemma coherentPointTotalTerminalKanMap_unit (B : SSet.{u}) :
    F2.continuousKanReplacementUnit.app (smallLeftUnstraightening
      (SSet.const pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _)) ≫
        coherentPointTotalTerminalKanMap B = stdSimplex.isTerminalObj₀.from _ :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

/-- sifted な底では、元の定値一点図式の余極限模型から一点への比較は同値。 -/
lemma coherentPointTotalTerminalKanMap_isQCatEquivalence (B : SSet.{u}) [IsSiftedInfinity B] :
    IsQCatEquivalence (coherentPointTotalTerminalKanMap B) :=
  (coherentPointTotalKanProjection_isSimplicialHomotopyEquivalence B).isQCatEquivalence.comp
    (siftedTerminalKanMap_isQCatEquivalence B)

/-- sifted な底上の定値終対象図式の、元の余極限余錐の頂点は終対象。 -/
lemma siftedCoherentPointTotalVertex_isTerminal (B : SSet.{u}) [IsSiftedInfinity B] :
    IsTerminalVertex (F2.coherentDiagramTotalCocone
      (SSet.const pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _)).vertex := by
  have h := coherentKanEdge_isInvertible_of_isQCatEquivalence
    (coherentPointTotalTerminalKanMap_isQCatEquivalence B)
  have : IsIso (Truncated.HomotopyCategory.homMk
    (coherentNerveEdge (coherentPointTotalTerminalKanMap B)).toTruncated) := h
  let e := asIso (Truncated.HomotopyCategory.homMk
    (coherentNerveEdge (coherentPointTotalTerminalKanMap B)).toTruncated)
  have ht : IsTerminalVertex (coherentNerveVertex pointKanObject.{u}) := by
    simpa only [pointSpaceVertex, spaceInfinityVertex_eq_coherent] using
      pointSpaceVertex_isTerminalVertex.{u}
  simpa only [F2.coherentDiagramTotalCocone_vertex, F2.coherentDiagramTotalVertex,
    spaceInfinityVertex_eq_coherent] using ht.of_vertexIso e.symm

/-- 元の定値終対象図式の余極限頂点を頂点にした、native な空積錐。 -/
def siftedCoherentEmptyProductNativeCone (B : SSet.{u}) :
    JoinCone (⊥ : SpaceInfinity.{u}.Subcomplex).ι :=
  emptyCone (F2.coherentDiagramTotalCocone
    (SSet.const pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _)).vertex

/-- sifted な余極限の元の頂点を保持する、空積保存。 -/
lemma siftedCoherentEmptyProductNativeCone_isLimit (B : SSet.{u}) [IsSiftedInfinity B] :
    IsLimitCone (siftedCoherentEmptyProductNativeCone B) :=
  (isLimitCone_emptyCone_iff _).mpr (siftedCoherentPointTotalVertex_isTerminal B)

end SerrePositivity.InfinityCategories.HomotopyLimits
