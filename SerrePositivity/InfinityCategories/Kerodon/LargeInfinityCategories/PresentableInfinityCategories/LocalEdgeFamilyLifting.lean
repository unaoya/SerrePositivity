module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeSectionRestrictionComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EdgeCosliceIntervalMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeHomLiftingFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibrationLocalFamily

/-!
概要：任意の coherent な局所辺の族について、元の相対 Hom の全境界充填性を証明する。
方針：元の比較射の可換性と Kan な写像空間の同値判定を使う。
規約：底と全パラメータは任意。使われ方：HTT 5.5.4.5(2) の局所辺の族の制限。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 点ごとの辺の局所性は、同じ底の相対 Hom の各持ち上げ fiber の可縮性を与える。 -/
lemma localEdgeFamily_vertexFiber_isContractibleKan {K X : SSet.{u}} [Quasicategory X]
    (f : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (z : X _⦋0⦌)
    (h : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] X).symm (f.app (Opposite.op ⦋0⦌) k)))) z)
    (sq : internalHom.PullbackObjObj (stdSimplex.δ (1 : Fin 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)))
    (k : K _⦋0⦌) (b : sq.pt _⦋0⦌)
    (hb : sq.snd.app (Opposite.op ⦋0⦌) b = f.app (Opposite.op ⦋0⦌) k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber sq.π b) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] X).symm (f.app (Opposite.op ⦋0⦌) k)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e = f.app (Opposite.op ⦋0⦌) k :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] X).apply_symm_apply _
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLocalForHom_edge_iff_sectionRestriction_trivial e z).mp (h k)
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeHomFiber_isContractibleKan_of_restriction_trivial
    (stdSimplex.δ (1 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z))
      sq e b (hb.trans he.symm)

/-- 任意の coherent な局所辺の族に対し、元の相対 Hom の族は全境界を持ち上げる。 -/
lemma localEdgeFamily_relativeHom_trivial {K X : SSet.{u}} [Quasicategory X]
    (f : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (z : X _⦋0⦌)
    (h : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] X).symm (f.app (Opposite.op ⦋0⦌) k)))) z)
    (sq : internalHom.PullbackObjObj (stdSimplex.δ (1 : Fin 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeHomFamilyProjection (stdSimplex.δ (1 : Fin 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)) sq f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeHomFamilyProjection_trivial _ _ _ _
    (localEdgeFamily_vertexFiber_isContractibleKan f z h sq)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
