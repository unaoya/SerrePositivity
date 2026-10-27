module

public import SerrePositivity.KST.Spectra.D3StageLoopCone
public import SerrePositivity.InfinityCategories.F1.Coherent.NerveHomEdgeNaturality

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
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3LoopSquareStageSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 実四角形の各角の評価は、元の角への実際の後合成。 -/
lemma d3SquareVertex_postcomp {X Y : SSet.{u + 1}}
    (S : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ X) (F : X ⟶ Y) (i j : Fin 2) :
    squareVertex (S ≫ F) i j = F.app (Opposite.op ⦋0⦌) (squareVertex S i j) := rfl

/-- 元の BF 辺の段評価は、同じ段射そのものの coherent な一次単体。 -/
lemma d3Stage_edge {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (coherentNerveMap (d3StageKanEnriched n)).app _ (coherentNerveEdge f).edge =
      (coherentNerveEdge (ObjectProperty.homMk (f.app n) :
        (d3StageKanEnriched n).obj X ⟶ (d3StageKanEnriched n).obj Y)).edge :=
  coherentNerveMap_edge_of_homEquiv _ f _ (d3Stage_vertex f n)

/-- 元の一点スペクトルの段頂点は、点つき Kan ∞ 圏の実零頂点。 -/
lemma d3StagePoint_isZero (n : ℕ) :
    IsZeroVertex (coherentNerveVertex ((d3StageKanEnriched.{u} n).obj spectrumPoint)) := by
  let Z := (d3StageKanEnriched.{u} n).obj spectrumPoint
  have hZ : IsIso Z.obj.hom := by
    change IsIso (𝟙 (𝟙_ SSet.{u}))
    infer_instance
  have hs (Y : PointedKanObject.{u}) : IsTerminal (SimplicialCategory.sHom Z Y) :=
    PointedZeroMapping.source_isTerminal Z.obj Y.obj
  have ht (Y : PointedKanObject.{u}) : IsTerminal (SimplicialCategory.sHom Y Z) :=
    PointedZeroMapping.target_isTerminal Y.obj Z.obj isTerminalTensorUnit
  refine ⟨?_, coherentNerve_isTerminalVertex_of_enrichedTerminal Z ht⟩
  apply isInitialVertex_of_pinchedHomLeft_isContractibleKan
  intro z
  obtain ⟨Y, rfl⟩ := (coherentNerveVertexEquiv PointedKanObject.{u}).surjective z
  apply (pinchedHomLeftRightEquivalence _ _).symm.isContractibleKan
  exact (coherentHomEquivalence Z Y).isContractibleKan
    (ulift_isContractibleKan_of_isTerminal _ (hs Y))

/-- 元の BF path から一点への同じ段射を成分とする頂点同型。 -/
def d3StageBasedPathPointIso (Y : OmegaSpectrum.{u}) (n : ℕ) :
    VertexIso (coherentNerveVertex ((d3StageKanEnriched n).obj (basedPath Y)))
      (coherentNerveVertex ((d3StageKanEnriched n).obj spectrumPoint)) := by
  let f : (d3StageKanEnriched n).obj (basedPath Y) ⟶
      (d3StageKanEnriched n).obj spectrumPoint :=
    ObjectProperty.homMk ((basedPathToPoint Y).app n)
  haveI := pointedKanObject_edge_isInvertible_of_piIsomorphism f
    (basedPathToPoint_levelwise Y n)
  exact asIso (Truncated.HomotopyCategory.homMk (coherentNerveEdge f))

/-- 元の BF path の各段も、同じ指定比較を通じて実零頂点。 -/
lemma d3StageBasedPath_isZero (Y : OmegaSpectrum.{u}) (n : ℕ) :
    IsZeroVertex (coherentNerveVertex ((d3StageKanEnriched n).obj (basedPath Y))) :=
  (d3StagePoint_isZero n).of_vertexIso (d3StageBasedPathPointIso Y n).symm

/-- 同じ共通実四角形を、元の厳密 tail の段を終点とする実 loop 四角形へ評価。 -/
def commonLoopSquare_stage (X : OmegaSpectrum.{u}) (n : ℕ) :
    LoopSquare (coherentNerveVertex ((d3StageKanEnriched n).obj (tail X))) := by
  let F := (commonLoopSquare X).square ≫ coherentNerveMap (d3StageKanEnriched n)
  have hp : squareVertex (commonLoopSquare X).square 0 1 = coherentNerveVertex spectrumPoint := by
    rw [← squareTopEdge_source, commonLoopSquare_top, Equiv.apply_symm_apply]
    exact (coherentNerveEdge (fromPoint (tail X))).src_eq
  have hb : squareVertex (commonLoopSquare X).square 1 0 =
      coherentNerveVertex (basedPath (tail X)) := by
    rw [← squareRightEdge_source, commonLoopSquare_right, Equiv.apply_symm_apply]
    exact (coherentNerveEdge (basedPathProjection (tail X))).src_eq
  refine { square := F
           zero_corner := ?_
           target_eq := ?_
           other_zero := ?_
           isPullback := commonLoopSquare_stage_isPullback X n }
  · change IsZeroVertex (squareVertex (_ ≫ _) 0 1)
    rw [d3SquareVertex_postcomp, hp, coherentNerveMap_vertex]
    exact d3StagePoint_isZero n
  · change squareVertex (_ ≫ _) 1 1 = _
    rw [d3SquareVertex_postcomp, (commonLoopSquare X).target_eq, coherentNerveMap_vertex]
  · change IsZeroVertex (squareVertex (_ ≫ _) 1 0)
    rw [d3SquareVertex_postcomp, hb, coherentNerveMap_vertex]
    exact d3StageBasedPath_isZero (tail X) n

/-- 同じ段 loop 四角形の実始点は、元の共通 BF 対象の同じ段。 -/
lemma commonLoopSquare_stage_vertex (X : OmegaSpectrum.{u}) (n : ℕ) :
    (commonLoopSquare_stage X n).vertex =
      coherentNerveVertex ((d3StageKanEnriched n).obj (commonRefinement X)) := by
  change squareVertex ((commonLoopSquare X).square ≫ _) 0 0 = _
  rw [d3SquareVertex_postcomp]
  change (coherentNerveMap (d3StageKanEnriched n)).app _ (commonLoopSquare X).vertex = _
  rw [commonLoopSquare_vertex, coherentNerveMap_vertex]

/-- 元の path 終点射の段射そのものを、同じ段四角形の右辺として保持する。 -/
lemma commonLoopSquare_stage_right (X : OmegaSpectrum.{u}) (n : ℕ) :
    squareRightEdge ≫ (commonLoopSquare_stage X n).square =
      SSet.yonedaEquiv.symm (coherentNerveEdge
        (ObjectProperty.homMk ((basedPathProjection (tail X)).app n) :
          (d3StageKanEnriched n).obj (basedPath (tail X)) ⟶
            (d3StageKanEnriched n).obj (tail X))).edge := by
  change squareRightEdge ≫ ((commonLoopSquare X).square ≫ _) = _
  rw [← Category.assoc, commonLoopSquare_right]
  exact (SSet.yonedaEquiv_symm_comp _ _).trans
    (congrArg SSet.yonedaEquiv.symm (d3Stage_edge (basedPathProjection (tail X)) n))

/-- 元の一点からの段射そのものを、同じ段四角形の上辺として保持する。 -/
lemma commonLoopSquare_stage_top (X : OmegaSpectrum.{u}) (n : ℕ) :
    squareTopEdge ≫ (commonLoopSquare_stage X n).square =
      SSet.yonedaEquiv.symm (coherentNerveEdge
        (ObjectProperty.homMk ((fromPoint (tail X)).app n) :
          (d3StageKanEnriched n).obj spectrumPoint ⟶
            (d3StageKanEnriched n).obj (tail X))).edge := by
  change squareTopEdge ≫ ((commonLoopSquare X).square ≫ _) = _
  rw [← Category.assoc, commonLoopSquare_top]
  exact (SSet.yonedaEquiv_symm_comp _ _).trans
    (congrArg SSet.yonedaEquiv.symm (d3Stage_edge (fromPoint (tail X)) n))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
