module

public import SerrePositivity.KST.Spectra.D3EndpointParameterSquare
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerSquareSpan

/-!
概要：実端点パラメータ族の両零角を、同じ元の point・path Hom から認証する。
方針：point Hom の実同型と path から一点への全単射 RLP を同じ Kan 辺へ移す。
規約：BF path の段とは区別し、通常の点つき Kan path 自体を使用する。
使われ方：d3 の標準端点図式族の loopDiagrams への因子化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3EndpointZeroSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の点つき Kan 一点。元の一点スペクトルの段と同じ対象。 -/
abbrev d3PointedKanPoint : PointedKanObject.{u} := (d3StageKanEnriched 0).obj spectrumPoint

/-- 同じ実一点は点つき Kan ∞ 圏の零頂点。 -/
lemma d3PointedKanPoint_isZero :
    IsZeroVertex (coherentNerveVertex d3PointedKanPoint.{u}) := d3StagePoint_isZero 0

/-- 元の実一点への同じ通常同型を、Kan ∞ 圏の頂点同型へ移す。 -/
def d3PointedKanPointIso (X : PointedKanObject.{u})
    (e : X.obj ≅ PointedObject.point) :
    VertexIso (coherentNerveVertex X) (coherentNerveVertex d3PointedKanPoint.{u}) := by
  let f : X ⟶ d3PointedKanPoint := ObjectProperty.homMk e.hom
  have h : _root_.SerrePositivity.InfinityCategories.Kan.KanPiIsomorphism f.hom.right := by
    change _root_.SerrePositivity.InfinityCategories.Kan.KanPiIsomorphism e.hom.right
    exact _root_.SerrePositivity.InfinityCategories.F1.Pointed.kanPiIsomorphism_of_monoRight _
      ((MorphismProperty.monomorphisms SSet.{u}).rlp_of_isIso _)
  haveI := pointedKanObject_edge_isInvertible_of_piIsomorphism f h
  exact asIso (Truncated.HomotopyCategory.homMk (coherentNerveEdge f))

/-- 通常の一点パラメータからの Hom は、同じ point 同型を通じて実零頂点。 -/
lemma d3PointedKanHomPoint_isZero (X : PointedKanObject.{u}) :
    IsZeroVertex (coherentNerveVertex ((d3PointedKanIhom PointedObject.point).obj X)) := by
  let e := (pointedHomPoint_isZero X.obj).iso PointedObject.point_isZero
  exact d3PointedKanPoint_isZero.of_vertexIso
    (d3PointedKanPointIso ((d3PointedKanIhom PointedObject.point).obj X) e).symm

/-- 通常の based path から一点への同じ全単射 RLP 射による頂点同型。 -/
def d3PointedKanPathPointIso (X : PointedKanObject.{u}) :
    VertexIso (coherentNerveVertex ((d3PointedKanIhom _root_.SerrePositivity.InfinityCategories.F1.Pointed.pointedInterval).obj X))
      (coherentNerveVertex d3PointedKanPoint.{u}) := by
  let f : (d3PointedKanIhom _root_.SerrePositivity.InfinityCategories.F1.Pointed.pointedInterval).obj X ⟶ d3PointedKanPoint :=
    ObjectProperty.homMk (PointedObject.toPoint (basedPathSpace X.obj))
  have h : _root_.SerrePositivity.InfinityCategories.Kan.KanPiIsomorphism f.hom.right :=
    _root_.SerrePositivity.InfinityCategories.F1.Pointed.kanPiIsomorphism_of_monoRight _ (basedPathSpace_toPoint_rlp X.obj)
  haveI := pointedKanObject_edge_isInvertible_of_piIsomorphism f h
  exact asIso (Truncated.HomotopyCategory.homMk (coherentNerveEdge f))

/-- 同じ通常 based path は、BF 置換を介さず実零頂点。 -/
lemma d3PointedKanPath_isZero (X : PointedKanObject.{u}) :
    IsZeroVertex (coherentNerveVertex ((d3PointedKanIhom _root_.SerrePositivity.InfinityCategories.F1.Pointed.pointedInterval).obj X)) :=
  d3PointedKanPoint_isZero.of_vertexIso (d3PointedKanPathPointIso X).symm

/-- 実端点パラメータ全四角形族の、各角の実頂点。 -/
lemma d3EndpointParameterSquare_corner (X : PointedKanObject.{u}) (i j : Fin 2) :
    squareVertex (squareDiagram
      (d3EndpointParameterSquare.app _ (coherentNerveVertex X))) i j =
        coherentNerveVertex ((d3PointedKanIhom (d3EndpointParameterObj (i, j))).obj X) := by
  rw [← squareDiagram_vertex_evaluation]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (d3PointedKanParameterSquare_corner d3EndpointParameter i j) (Opposite.op ⦋0⦌))
      (coherentNerveVertex X)
  exact h.trans (coherentNerveMap_vertex _ X)

/-- 構成済み全族の point 角は、同じ point Hom の実零頂点。 -/
lemma d3EndpointParameterSquare_zero_corner (X : PointedKanObject.{u}) :
    IsZeroVertex (squareVertex (squareDiagram
      (d3EndpointParameterSquare.app _ (coherentNerveVertex X))) 0 1) := by
  rw [d3EndpointParameterSquare_corner]
  exact d3PointedKanHomPoint_isZero X

/-- 構成済み全族の path 角は、同じ通常 path Hom の実零頂点。 -/
lemma d3EndpointParameterSquare_other_zero (X : PointedKanObject.{u}) :
    IsZeroVertex (squareVertex (squareDiagram
      (d3EndpointParameterSquare.app _ (coherentNerveVertex X))) 1 0) := by
  rw [d3EndpointParameterSquare_corner]
  exact d3PointedKanPath_isZero X

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
