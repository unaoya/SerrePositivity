module

public import SerrePositivity.KST.Spectra.EndpointLoopComparison
public import SerrePositivity.KST.Spectra.PointedEndpointLoopPullback
public import SerrePositivity.KST.Spectra.PointedPullbackChange

/-!
概要：円の BF cotensor から具体的な native loop 対象への比較は実際の Sp の同値。
方針：各段で BF path の置換射影を引き戻し、置換前の円の写像対象との同型へ戻す。
規約：比較射そのものの全基点 π 同型と可逆性を示す。使われ方：Sp の loop の具体的な模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop

/-- native loop の各段から、置換前の path の引き戻しへの実際の比較。 -/
def rawComparison (Y : OmegaSpectrum.{u}) (n : ℕ) : ((obj Y).level n).space ⟶
    pullback (pathEndpoint (Y.level n).space) (PointedObject.fromPoint (Y.level n).space) :=
  PointedPullbackChange.map ((cotensorProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y).app n)
    (pathEndpoint (Y.level n).space) (PointedObject.fromPoint (Y.level n).space)

@[reassoc]
lemma rawComparison_fst (Y : OmegaSpectrum.{u}) (n : ℕ) :
    rawComparison Y n ≫ pullback.fst (pathEndpoint (Y.level n).space)
        (PointedObject.fromPoint (Y.level n).space) =
      (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackFst (basedPathProjection Y) (fromPoint Y)).app n ≫
        (cotensorProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y).app n :=
  PointedPullbackChange.map_fst _ _ _

lemma rawComparison_rlp (Y : OmegaSpectrum.{u}) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (rawComparison Y n).right :=
  PointedPullbackChange.map_rlp _ _ _
    (KanSequence.replacementStage
      (KanSequence.mapping _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} Y.toKanSequence) n).projection_rlp

/-- 実際の BF loop 比較を置換前へ戻すと、元の円の射影と pullback 同型の合成となる。 -/
lemma comparison_raw (Y : OmegaSpectrum.{u}) (n : ℕ) :
    (comparison Y).app n ≫ rawComparison Y n =
      (cotensorProjection endpointCircle Y).app n ≫
        (pointedEndpointLoopIso (Y.level n).space).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, rawComparison_fst, ← Category.assoc]
    have hf := congrArg
      (fun t : cotensor endpointCircle Y ⟶ basedPath Y ↦ t.app n) (comparison_fst Y)
    change (comparison Y).app n ≫
      (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackFst (basedPathProjection Y) (fromPoint Y)).app n = _ at hf
    rw [hf, endpointLoopToPath_comparison, Category.assoc, pointedEndpointLoopIso_hom_fst]
  · exact PointedObject.point_isZero.eq_of_tgt _ _

/-- 比較射の各段は全基点・全次数で π 同型。 -/
lemma comparison_levelwise (Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((comparison Y).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := (rawComparison Y n).right) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (rawComparison_rlp Y n))
  have h := congrArg Under.Hom.right (comparison_raw Y n)
  simp only [Under.comp_right] at h
  rw [h]
  exact (cotensorProjection_piIsomorphism endpointCircle Y n).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
      (X := (PointedObject.basedHom endpointCircle (Y.level n).space).right)
      (Y := (pullback (pathEndpoint (Y.level n).space)
        (PointedObject.fromPoint (Y.level n).space)).right)
      (PointedSimplicialSet.forget.mapIso (pointedEndpointLoopIso (Y.level n).space)))

local instance endpointLoopSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance endpointLoopHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 元の BF loop 比較の辺自体が Sp の同値。 -/
lemma comparison_isInvertible (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (comparison Y)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (comparison_levelwise Y)

/-- 円の BF cotensor は元の Sp の実際の loop 四角形の頂点に同値。 -/
def endpointLoopVertexIso (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor endpointCircle Y)) (square Y).vertex := by
  rw [square_vertex]
  haveI := comparison_isInvertible Y
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (comparison Y)))

end SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop
