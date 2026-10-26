module

public import SerrePositivity.KST.Spectra.D3LoopSourceComparison
public import SerrePositivity.InfinityCategories.Stable.LimitConeVertexTransport

/-!
概要：構成した BF 始点を実頂点とする、厳密 tail 終点の実 loop 錐を作る。
方針：固定した元の cospan の slice の右 fibration に、指定右脚そのものを持ち上げる。
規約：錐比較の像は同じ BF 右脚。点別頂点同型だけで極限性を結論しない。
使われ方：d3b② の共通解像に保持する実 loop 図式と元の比較射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance loopSourceConeSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance loopSourceConeHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 実 loop 錐へ持ち上げる辺は、元の実 BF 右脚そのもの。 -/
def loopSourceConeApexEdge (X : OmegaSpectrum.{u}) :
    Truncated.Edge (X := (truncation 2).obj Sp.{u})
      (coherentNerveVertex (loopSource X)) (BasedLoop.cone (tail X)).vertex :=
  ⟨(coherentNerveEdge (loopSourceToBasedLoop X)).edge,
    (coherentNerveEdge (loopSourceToBasedLoop X)).src_eq,
    (coherentNerveEdge (loopSourceToBasedLoop X)).tgt_eq.trans
      (BasedLoop.cone_vertex (tail X)).symm⟩

/-- 指定 BF 右脚は、錐の頂点に読み替えても同じ可逆辺。 -/
lemma loopSourceConeApexEdge_isInvertible (X : OmegaSpectrum.{u}) :
    IsInvertibleEdge (loopSourceConeApexEdge X) :=
  (isInvertibleEdge_congr (e := loopSourceConeApexEdge X)
    (f := (coherentNerveEdge (loopSourceToBasedLoop X)).toTruncated) rfl).2
      (loopSourceToBasedLoop_isInvertible X)

/-- 固定した元の cospan の上で、同じ実 BF 右脚を持ち上げた錐の比較。 -/
def loopSourceConeLift (X : OmegaSpectrum.{u}) :
    (Δ[1] : SSet.{u + 1}) ⟶ sliceOver (BasedLoop.diagram (tail X)) :=
  Classical.choose (rightFibration_liftEdge_target
    (sliceOverProjection (BasedLoop.diagram (tail X))) (BasedLoop.cone (tail X))
    (loopSourceConeApexEdge X))

/-- 持ち上げの終端は元の実 loop 錐に厳密一致する。 -/
lemma loopSourceConeLift_target (X : OmegaSpectrum.{u}) :
    stdSimplex.δ 0 ≫ loopSourceConeLift X = SSet.yonedaEquiv.symm (BasedLoop.cone (tail X)) :=
  (Classical.choose_spec (rightFibration_liftEdge_target
    (sliceOverProjection (BasedLoop.diagram (tail X))) (BasedLoop.cone (tail X))
    (loopSourceConeApexEdge X))).1

/-- 錐比較全体の apex 像は元の実 BF 右脚の同じ一次単体。 -/
lemma loopSourceConeLift_projection (X : OmegaSpectrum.{u}) :
    loopSourceConeLift X ≫ sliceOverProjection (BasedLoop.diagram (tail X)) =
      SSet.yonedaEquiv.symm (coherentNerveEdge (loopSourceToBasedLoop X)).edge :=
  (Classical.choose_spec (rightFibration_liftEdge_target
    (sliceOverProjection (BasedLoop.diagram (tail X))) (BasedLoop.cone (tail X))
    (loopSourceConeApexEdge X))).2

/-- 同じ持ち上げの始端となる、固定した元の cospan 上の実錐。 -/
def loopSourceCone (X : OmegaSpectrum.{u}) : JoinCone (BasedLoop.diagram (tail X)) :=
  (sliceOver (BasedLoop.diagram (tail X))).δ 1 (SSet.yonedaEquiv (loopSourceConeLift X))

/-- 実錐から元の実 loop 錐への同じ比較辺。 -/
def loopSourceConeEdge (X : OmegaSpectrum.{u}) :
    Truncated.Edge (X := (truncation 2).obj (sliceOver (BasedLoop.diagram (tail X))))
      (loopSourceCone X) (BasedLoop.cone (tail X)) :=
  ⟨SSet.yonedaEquiv (loopSourceConeLift X), rfl, by
    change (sliceOver (BasedLoop.diagram (tail X))).δ 0
      (SSet.yonedaEquiv (loopSourceConeLift X)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, loopSourceConeLift_target, Equiv.apply_symm_apply]⟩

/-- 錐比較辺の頂点射影は、選び直した同値でなく元の BF 右脚。 -/
lemma loopSourceConeEdge_projection (X : OmegaSpectrum.{u}) :
    ((loopSourceConeEdge X).map
      ((truncation 2).map (sliceOverProjection (BasedLoop.diagram (tail X))))).edge =
      (coherentNerveEdge (loopSourceToBasedLoop X)).edge := by
  change (sliceOverProjection (BasedLoop.diagram (tail X))).app _
    (SSet.yonedaEquiv (loopSourceConeLift X)) = _
  rw [← SSet.yonedaEquiv_comp, loopSourceConeLift_projection, Equiv.apply_symm_apply]

/-- 同じ錐比較の可逆性を右 fibration の反映で認証する。 -/
lemma loopSourceConeEdge_isInvertible (X : OmegaSpectrum.{u}) :
    IsInvertibleEdge (X := sliceOver (BasedLoop.diagram (tail X))) (loopSourceConeEdge X) :=
  derived_rightFibration_reflects_invertibleEdge
    (sliceOverProjection (BasedLoop.diagram (tail X))) (loopSourceConeEdge X)
    ((isInvertibleEdge_congr (loopSourceConeEdge_projection X)).2
      (loopSourceToBasedLoop_isInvertible X))

/-- 元の錐全体との指定同型。apex だけの同型ではない。 -/
def loopSourceConeIso (X : OmegaSpectrum.{u}) :
    VertexIso (X := sliceOver (BasedLoop.diagram (tail X)))
      (loopSourceCone X) (BasedLoop.cone (tail X)) := by
  haveI := loopSourceConeEdge_isInvertible X
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (loopSourceConeEdge X))

/-- 実錐の頂点は、元の BF 始点 L_X に厳密一致する。 -/
lemma loopSourceCone_vertex (X : OmegaSpectrum.{u}) :
    (loopSourceCone X).vertex = coherentNerveVertex (loopSource X) := by
  have ht := congrArg (fun z ↦ Sp.δ 1 z) (loopSourceConeEdge_projection X)
  have hn := ConcreteCategory.congr_hom
    ((sliceOverProjection (BasedLoop.diagram (tail X))).naturality
      (SimplexCategory.δ (1 : Fin 2)).op)
    (SSet.yonedaEquiv (loopSourceConeLift X))
  exact hn.trans (ht.trans (coherentNerveEdge (loopSourceToBasedLoop X)).src_eq)

/-- 元の cospan を保つ錐全体の同型から、同じ実錐の極限性を証明する。 -/
lemma loopSourceCone_isLimit (X : OmegaSpectrum.{u}) : IsLimitCone (loopSourceCone X) :=
  (BasedLoop.cone_isLimit (tail X)).of_vertexIso (loopSourceConeIso X).symm

/-- L_X を実始点とし、元の厳密 tail を終点とする実 loop 四角形。 -/
def loopSourceSquare (X : OmegaSpectrum.{u}) : LoopSquare (coherentNerveVertex (tail X)) := by
  let F := coneSquare (loopSourceCone X)
  have hr : squareRightEdge ≫ F =
      SSet.yonedaEquiv.symm (coherentNerveEdge (basedPathProjection (tail X))).edge := by
    rw [coneSquare_right, BasedLoop.diagram, edgeCospan_left]
    rfl
  have ht : squareTopEdge ≫ F =
      SSet.yonedaEquiv.symm (coherentNerveEdge (fromPoint (tail X))).edge := by
    rw [coneSquare_top, BasedLoop.diagram, edgeCospan_right]
    rfl
  have hv : squareVertex F 1 1 = coherentNerveVertex (tail X) := by
    rw [← squareRightEdge_target, hr, Equiv.apply_symm_apply]
    exact (coherentNerveEdge (basedPathProjection (tail X))).tgt_eq
  have h₀ : squareVertex F 1 0 = coherentNerveVertex (basedPath (tail X)) := by
    rw [← squareRightEdge_source, hr, Equiv.apply_symm_apply]
    exact (coherentNerveEdge (basedPathProjection (tail X))).src_eq
  have h₁ : squareVertex F 0 1 = coherentNerveVertex spectrumPoint := by
    rw [← squareTopEdge_source, ht, Equiv.apply_symm_apply]
    exact (coherentNerveEdge (fromPoint (tail X))).src_eq
  exact { square := F
          zero_corner := h₁.symm ▸ pointZeroVertex.isZero
          target_eq := hv
          other_zero := h₀.symm ▸ basedPath_isZeroVertex (tail X)
          isPullback := coneSquare_isPullback _ (loopSourceCone_isLimit X) }

/-- 同じ実 loop 四角形の始点は L_X 自体。 -/
lemma loopSourceSquare_vertex (X : OmegaSpectrum.{u}) :
    (loopSourceSquare X).vertex = coherentNerveVertex (loopSource X) := by
  change squareVertex (coneSquare (loopSourceCone X)) 0 0 = _
  rw [coneSquare_vertex, loopSourceCone_vertex]

/-- 元の固定 cospan を保つ錐比較を、実四角形全体の FunctorIso へ移す。 -/
def loopSourceSquareFunctorIso (X : OmegaSpectrum.{u}) :
    FunctorIso (loopSourceSquare X).square (BasedLoop.square (tail X)).square := by
  have e := VertexIso.map (loopSourceConeIso X)
    (sliceSquareDiagramMap (BasedLoop.diagram (tail X)))
  rw [sliceSquareDiagramMap_vertex, sliceSquareDiagramMap_vertex] at e
  exact e

/-- 実四角形の右辺は元の厳密 tail の path 終点射。 -/
lemma loopSourceSquare_right (X : OmegaSpectrum.{u}) :
    squareRightEdge ≫ (loopSourceSquare X).square =
      SSet.yonedaEquiv.symm (coherentNerveEdge (basedPathProjection (tail X))).edge := by
  change squareRightEdge ≫ coneSquare (loopSourceCone X) = _
  rw [coneSquare_right, BasedLoop.diagram, edgeCospan_left]
  rfl

/-- 実四角形の上辺も元の厳密 tail への一点からの射。 -/
lemma loopSourceSquare_top (X : OmegaSpectrum.{u}) :
    squareTopEdge ≫ (loopSourceSquare X).square =
      SSet.yonedaEquiv.symm (coherentNerveEdge (fromPoint (tail X))).edge := by
  change squareTopEdge ≫ coneSquare (loopSourceCone X) = _
  rw [coneSquare_top, BasedLoop.diagram, edgeCospan_right]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
