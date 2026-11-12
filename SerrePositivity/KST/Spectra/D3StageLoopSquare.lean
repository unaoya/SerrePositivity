module

public import SerrePositivity.KST.Spectra.D3StageLoopCone
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality

/-!
概要：元の共通実 loop 四角形を各段の実 loop 四角形へ移す。
方針：同じ錐の段極限性、点つき一点の豊穣零性、元の path の段比較を使う。
規約：始点・終点・両零角と二辺を保持。BF 全体の自然性は別工程。
使われ方：d3b② の実図式始点の段作用を比較する実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3LoopSquareStageSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 実四角形の各角の評価は、元の角への実際の後合成。 -/
lemma d3SquareVertex_postcomp {X Y : SSet.{u + 1}}
    (S : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ X) (F : X ⟶ Y) (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (S ≫ F) i j = F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex S i j) := rfl

/-- 元の BF 辺の段評価は、同じ段射そのものの coherent な一次単体。 -/
lemma d3Stage_edge {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (ObjectProperty.homMk (f.app n) :
        (d3StageKanEnriched n).obj X ⟶ (d3StageKanEnriched n).obj Y)).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv _ f _ (d3Stage_vertex f n)

/-- 元の一点スペクトルの段頂点は、点つき Kan ∞ 圏の実零頂点。 -/
lemma d3StagePoint_isZero (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((d3StageKanEnriched.{u} n).obj _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint)) := by
  let Z := (d3StageKanEnriched.{u} n).obj _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint
  have hZ : IsIso Z.obj.hom := by
    change IsIso (𝟙 (𝟙_ SSet.{u}))
    infer_instance
  have hs (Y : PointedKanObject.{u}) : IsTerminal (SimplicialCategory.sHom Z Y) :=
    PointedZeroMapping.source_isTerminal Z.obj Y.obj
  have ht (Y : PointedKanObject.{u}) : IsTerminal (SimplicialCategory.sHom Y Z) :=
    PointedZeroMapping.target_isTerminal Y.obj Z.obj isTerminalTensorUnit
  refine ⟨?_, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentNerve_isTerminalVertex_of_enrichedTerminal Z ht⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_of_pinchedHomLeft_isContractibleKan
  intro z
  obtain ⟨Y, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv PointedKanObject.{u}).surjective z
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftRightEquivalence _ _).symm.isContractibleKan
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence Z Y).isContractibleKan
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ulift_isContractibleKan_of_isTerminal _ (hs Y))

/-- 元の BF path から一点への同じ段射を成分とする頂点同型。 -/
def d3StageBasedPathPointIso (Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((d3StageKanEnriched n).obj (basedPath Y)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((d3StageKanEnriched n).obj _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint)) := by
  let f : (d3StageKanEnriched n).obj (basedPath Y) ⟶
      (d3StageKanEnriched n).obj _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint :=
    ObjectProperty.homMk ((basedPathToPoint Y).app n)
  haveI := pointedKanObject_edge_isInvertible_of_piIsomorphism f
    (basedPathToPoint_levelwise Y n)
  exact asIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f))

/-- 元の BF path の各段も、同じ指定比較を通じて実零頂点。 -/
lemma d3StageBasedPath_isZero (Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((d3StageKanEnriched n).obj (basedPath Y))) :=
  (d3StagePoint_isZero n).of_vertexIso (d3StageBasedPathPointIso Y n).symm

/-- 同じ共通実四角形を、元の厳密 tail の段を終点とする実 loop 四角形へ評価。 -/
def commonLoopSquare_stage (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((d3StageKanEnriched n).obj (tail X))) := by
  let F := (commonLoopSquare X).square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n)
  have hp : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (commonLoopSquare X).square 0 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source, commonLoopSquare_top, Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fromPoint (tail X))).src_eq
  have hb : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (commonLoopSquare X).square 1 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (basedPath (tail X)) := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source, commonLoopSquare_right, Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (basedPathProjection (tail X))).src_eq
  refine { square := F
           zero_corner := ?_
           target_eq := ?_
           other_zero := ?_
           isPullback := commonLoopSquare_stage_isPullback X n }
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_ ≫ _) 0 1)
    rw [d3SquareVertex_postcomp, hp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
    exact d3StagePoint_isZero n
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_ ≫ _) 1 1 = _
    rw [d3SquareVertex_postcomp, (commonLoopSquare X).target_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_ ≫ _) 1 0)
    rw [d3SquareVertex_postcomp, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
    exact d3StageBasedPath_isZero (tail X) n

/-- 同じ段 loop 四角形の実始点は、元の共通 BF 対象の同じ段。 -/
lemma commonLoopSquare_stage_vertex (X : OmegaSpectrum.{u}) (n : ℕ) :
    (commonLoopSquare_stage X n).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((d3StageKanEnriched n).obj (commonRefinement X)) := by
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((commonLoopSquare X).square ≫ _) 0 0 = _
  rw [d3SquareVertex_postcomp]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n)).app _ (commonLoopSquare X).vertex = _
  rw [commonLoopSquare_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]

/-- 元の path 終点射の段射そのものを、同じ段四角形の右辺として保持する。 -/
lemma commonLoopSquare_stage_right (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (commonLoopSquare_stage X n).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (ObjectProperty.homMk ((basedPathProjection (tail X)).app n) :
          (d3StageKanEnriched n).obj (basedPath (tail X)) ⟶
            (d3StageKanEnriched n).obj (tail X))).edge := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ ((commonLoopSquare X).square ≫ _) = _
  rw [← Category.assoc, commonLoopSquare_right]
  exact (SSet.yonedaEquiv_symm_comp _ _).trans
    (congrArg SSet.yonedaEquiv.symm (d3Stage_edge (basedPathProjection (tail X)) n))

/-- 元の一点からの段射そのものを、同じ段四角形の上辺として保持する。 -/
lemma commonLoopSquare_stage_top (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (commonLoopSquare_stage X n).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (ObjectProperty.homMk ((fromPoint (tail X)).app n) :
          (d3StageKanEnriched n).obj _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint ⟶
            (d3StageKanEnriched n).obj (tail X))).edge := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ ((commonLoopSquare X).square ≫ _) = _
  rw [← Category.assoc, commonLoopSquare_top]
  exact (SSet.yonedaEquiv_symm_comp _ _).trans
    (congrArg SSet.yonedaEquiv.symm (d3Stage_edge (fromPoint (tail X)) n))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
