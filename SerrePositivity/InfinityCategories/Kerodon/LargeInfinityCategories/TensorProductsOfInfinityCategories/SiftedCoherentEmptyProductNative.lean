module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedEmptyProductNative

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentPointTotalProjection
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalCocone

/-!
概要：定値終対象 coherent 図式の元の余極限頂点は、sifted な底上で終対象。
方針：元の小さい全空間の射影を Kan 置換し、底の一点比較へ合成する。
規約：頂点は元の coherentDiagramTotalCocone の頂点を使う。
使われ方：sifted な空間値余極限の空積保存。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-- 定値一点図式の元の余極限 Kan 模型から一点への比較は、元の射影の像。 -/
def coherentPointTotalTerminalKanMap (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject
      (SSet.const _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection
    (SSet.const _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedTerminalKanMap B

/-- 同じ比較は元の全空間の Kan 置換単位と厳密に可換。 -/
lemma coherentPointTotalTerminalKanMap_unit (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening
      (SSet.const _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _)) ≫
        coherentPointTotalTerminalKanMap B = stdSimplex.isTerminalObj₀.from _ :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

/-- sifted な底では、元の定値一点図式の余極限模型から一点への比較は同値。 -/
lemma coherentPointTotalTerminalKanMap_isQCatEquivalence (B : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coherentPointTotalTerminalKanMap B) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentPointTotalKanProjection_isSimplicialHomotopyEquivalence B).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedTerminalKanMap_isQCatEquivalence B)

/-- sifted な底上の定値終対象図式の、元の余極限余錐の頂点は終対象。 -/
lemma siftedCoherentPointTotalVertex_isTerminal (B : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone
      (SSet.const _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _)).vertex := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
    (coherentPointTotalTerminalKanMap_isQCatEquivalence B)
  have : IsIso (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (coherentPointTotalTerminalKanMap B)).toTruncated) := h
  let e := asIso (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (coherentPointTotalTerminalKanMap B)).toTruncated)
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.{u}) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pointSpaceVertex_isTerminalVertex.{u}
  simpa only [_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex, _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent] using ht.of_vertexIso e.symm

/-- 元の定値終対象図式の余極限頂点を頂点にした、native な空積錐。 -/
def siftedCoherentEmptyProductNativeCone (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (⊥ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.Subcomplex).ι :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.emptyCone (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone
    (SSet.const _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _)).vertex

/-- sifted な余極限の元の頂点を保持する、空積保存。 -/
lemma siftedCoherentEmptyProductNativeCone_isLimit (B : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (siftedCoherentEmptyProductNativeCone B) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_emptyCone_iff _).mpr (siftedCoherentPointTotalVertex_isTerminal B)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.8.11" (partial := special) "仮定：有限積と K 余極限を持ち積が各変数でそれを保つ準圏（Lean が強い：Space の場合）。結論：coherent 空間図式の元の余極限と二項積・空積の比較が実際の極限錐となる（この場合に有限積保存と一致）。任意 X の積保存を仮定して同じ比較を一般化したとはしない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentEmptyProductNativeCone_isLimit
attribute [cite HTT "5.5.8.12" (partial := component) "仮定：小 sifted K（HTT と一致）。結論：Space の元の coherent K 余極限の積・空積との交換（本文の空間の場合に一致）。任意の ∞-topos で各変数の積が余極限を保存するという後半の拡張は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentEmptyProductNativeCone_isLimit
