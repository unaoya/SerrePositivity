module

public import SerrePositivity.KST.LocalizingInvariants.EquivalenceSpanTriangles
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization

/-!
概要：指定辺集合に左脚を持つ span の実単体集合と、反転関手による後合成を構成する。
方針：関手圏の全部分複体を使い、左脚の評価が後合成と可換であることを保持する。
規約：分母の可逆化以外の局所化普遍性は入力しない。
使われ方：分母付き span の族の三角形補完と写像空間への評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def spanLeftEdge {X : SSet.{u}} (v : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌) : X _⦋1⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) v)

lemma intervalFunctorVertexEdge_postcomp {X Y : SSet.{u}} (F : X ⟶ Y)
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((ihom (Δ[1] : SSet.{u})).map F).app (Opposite.op ⦋0⦌) v) =
      F.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v) := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) X).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ F)) =
    F.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex,
    SSet.yonedaEquiv_comp]

lemma spanLeftEdge_postcomp {X Y : SSet.{u}} (F : X ⟶ Y)
    (v : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌) :
    spanLeftEdge (((ihom (horn 2 0 : SSet.{u})).map F).app (Opposite.op ⦋0⦌) v) =
      F.app (Opposite.op ⦋1⦌) (spanLeftEdge v) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge
    (((ihom (horn 2 0 : SSet.{u})).map F ≫ (pre horn₂₀.ι₀₁).app Y).app
      (Opposite.op ⦋0⦌) v) = _
  rw [(pre horn₂₀.ι₀₁).naturality F]
  exact intervalFunctorVertexEdge_postcomp F _

def markedSpans (X : SSet.{u}) (W : Set (X _⦋1⦌)) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
    (fun v => spanLeftEdge v ∈ W) : SSet.{u})

def markedSpanInclusion (X : SSet.{u}) (W : Set (X _⦋1⦌)) :
    markedSpans X W ⟶ (ihom (horn 2 0 : SSet.{u})).obj X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (fun v => spanLeftEdge v ∈ W)).ι

def invertedSpanMap {X Q : SSet.{u}} (F : X ⟶ Q) (W : Set (X _⦋1⦌))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) : markedSpans X W ⟶ equivalenceSpans Q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsEquivalenceSpanVertex
    (markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F) (by
      intro v
      have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (spanLeftEdge
        (((ihom (horn 2 0 : SSet.{u})).map F).app (Opposite.op ⦋0⦌) v.val)))
      rw [spanLeftEdge_postcomp]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
        (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (spanLeftEdge v.val)).map ((truncation 2).map F))
        (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.app (Opposite.op ⦋1⦌) (spanLeftEdge v.val))) rfl).mp (hF hv))

lemma invertedSpanMap_inclusion {X Q : SSet.{u}} (F : X ⟶ Q) (W : Set (X _⦋1⦌))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) : invertedSpanMap F W hF ≫ equivalenceSpanInclusion Q =
      markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

end SerrePositivity.KST.LocalizingInvariants
