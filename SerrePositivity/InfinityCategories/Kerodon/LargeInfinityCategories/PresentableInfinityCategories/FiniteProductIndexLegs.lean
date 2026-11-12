module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoherentProjectionCocones
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteProductIndexTransport

/-!
概要：一般有限添字へ再添字した元の native 有限積錐の各脚と全余錐比較。
方針：元の脚の全一単体の一致から Kan 射の厳密な一致を回収し、元の全余錐比較を使う。
規約：元の頂点・脚・coherent 射影・指定単位を保持する。
使われ方：P_Σ の sifted 閉性の一般有限離散図式。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (n : ℕ) {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  {J : Type u} (e : J ≃ ULift.{u} (Fin (n + 1))) (j : Discrete J)

/-- 元の再添字錐の native な脚を、同じ元の余極限 Kan 対象の射に戻す。 -/
def reindexedFiniteProductNativeKanLeg :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductDiagram n F e).obj j :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductNativeCone n F e) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductNativeCone_vertex n F e) j

/-- 戻した再添字脚は、指定された元の脚そのもの。 -/
lemma reindexedFiniteProductNativeKanLeg_eq :
    reindexedFiniteProductNativeKanLeg n F e j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeKanLeg n F (Discrete.mk (e j.as)) := by
  have h : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLegEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductNativeCone n F e) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductNativeCone_vertex n F e) j =
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLegEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone n F) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone_vertex n F) (Discrete.mk (e j.as)) := by
    apply SSet.Edge.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductNativeCone_leg_edge n F e j
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom h

/-- 再添字した元の native 脚の Kan 像は、元の全空間射影の Kan 像にホモトピック。 -/
lemma reindexedFiniteProductNativeKanLeg_projection :
    Nonempty (SSet.Homotopy (reindexedFiniteProductNativeKanLeg n F e j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection n F (e j.as).down))) := by
  rw [reindexedFiniteProductNativeKanLeg_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeKanLeg_projection n F (Discrete.mk (e j.as))

/-- 元の再添字 native 脚の全余錐作用も、元の反復射影と指定単位の合成余錐に同型。 -/
def reindexedFiniteProductNativeCoconeIso
    (T : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitTriangle (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)
      (F (e j.as).down) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F (e j.as).down)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex (F (e j.as).down)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F))
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex (F (e j.as).down))).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F (e j.as).down)
            (reindexedFiniteProductNativeKanLeg n F e j)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F (e j.as).down)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F (e j.as).down) T)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex (F (e j.as).down))
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone_vertex _ _ _ T)) := by
  rw [reindexedFiniteProductNativeKanLeg_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCoconeIso n F (Discrete.mk (e j.as)) T

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
