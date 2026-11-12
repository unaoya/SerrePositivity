module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointPullbacks
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
概要：二方向端点図式の零角である point・based path のテンソルパラメータを認証する。
方針：通常閉圏の対象同型で元の point・based path Hom へ移し、既証の零性を使う。
規約：対象同型のみの利用で全関手自然性を推論しない。円交換因子を比較しない。
使われ方：実二方向図式の pullback 面を、両零角付きの実 loop 図式へ因子化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

private def d3EndpointVertexIsoOfIso (X Y : PointedKanObject.{u}) (e : X.obj ≅ Y.obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) := by
  let f : X ⟶ Y := ObjectProperty.homMk e.hom
  have h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.hom.right := by
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e.hom.right
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
      ((MorphismProperty.monomorphisms SSet.{u}).rlp_of_isIso _)
  haveI := pointedKanObject_edge_isInvertible_of_piIsomorphism f h
  exact asIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f))

private def d3TensorEndpointVertexIso (A B : PointedSimplicialSet.{u})
    (Y : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((d3PointedKanIhom (A ⊗ B)).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((d3PointedKanIhom B).obj ((d3PointedKanIhom A).obj Y))) :=
  d3EndpointVertexIsoOfIso _ _ (ihomCurryIso A B Y.obj)

/-- 任意の左パラメータと point のテンソルからの Hom は、同じ実零頂点。 -/
lemma d3PointedKanTensorPoint_isZero (A : PointedSimplicialSet.{u}) (Y : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      ((d3PointedKanIhom (A ⊗ PointedObject.point)).obj Y)) :=
  (d3PointedKanHomPoint_isZero ((d3PointedKanIhom A).obj Y)).of_vertexIso
    (d3TensorEndpointVertexIso A PointedObject.point Y).symm

/-- 任意の左パラメータと実 based interval のテンソルからの Hom も実零頂点。 -/
lemma d3PointedKanTensorPath_isZero (A : PointedSimplicialSet.{u}) (Y : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      ((d3PointedKanIhom (A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval)).obj Y)) :=
  (d3PointedKanPath_isZero ((d3PointedKanIhom A).obj Y)).of_vertexIso
    (d3TensorEndpointVertexIso A _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y).symm

/-- point が左因子にある場合も、同じテンソルパラメータの Hom は実零頂点。 -/
lemma d3PointedKanPointTensor_isZero (B : PointedSimplicialSet.{u}) (Y : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      ((d3PointedKanIhom (PointedObject.point ⊗ B)).obj Y)) := by
  let e := d3EndpointVertexIsoOfIso ((d3PointedKanIhom (PointedObject.point ⊗ B)).obj Y)
    ((d3PointedKanIhom (B ⊗ PointedObject.point)).obj Y)
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso (β_ B PointedObject.point) Y.obj)
  exact (d3PointedKanTensorPoint_isZero B Y).of_vertexIso e.symm

/-- based interval が左因子にある場合も、同じ実 path パラメータからの Hom は零頂点。 -/
lemma d3PointedKanPathTensor_isZero (B : PointedSimplicialSet.{u}) (Y : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      ((d3PointedKanIhom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval ⊗ B)).obj Y)) := by
  let e := d3EndpointVertexIsoOfIso ((d3PointedKanIhom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval ⊗ B)).obj Y)
    ((d3PointedKanIhom (B ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval)).obj Y)
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso (β_ B _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval) Y.obj)
  exact (d3PointedKanTensorPath_isZero B Y).of_vertexIso e.symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
