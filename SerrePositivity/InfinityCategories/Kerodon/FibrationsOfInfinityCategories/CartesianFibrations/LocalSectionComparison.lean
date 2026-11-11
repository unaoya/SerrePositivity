module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorBaseChangeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorPostEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalCoslicePrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFiberPrecomposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EdgeCosliceIntervalMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveInvertedHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPostcomposition

/-!
概要：局所対象の図式への表現可能 left fibration の切断の比較。
方針：局所対象の全部分圏へ底変換し、fiber ごとの同値を切断へ移す。
規約：図式の添字には quasicategory 性を要求しない。
使われ方：HTT 5.5.4 の局所対象の極限閉性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 相対切断の底変換は、元の底上の射による後合成と厳密に可換。 -/
lemma relativeFunctorBaseChangeForward_post {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (k : D ⟶ B) (a : A ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (pullback.snd p k) (pullback.snd q k)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf k)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection p q f hf k) a ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso q k a).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p k a).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf (a ≫ k) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom A).map q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ k))
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward q k a) ≫ _ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k a ≫ _) ≫ _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorBaseChangeForward_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost_ι, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost_ι,
    ← Category.assoc]
  conv_rhs => rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorBaseChangeForward_ι]
  simp only [Category.assoc, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange, pullback.lift_fst]

/-- 同値な fiber を持つ部分圏へ着地する任意の図式では、相対切断の後合成が同値。 -/
lemma relativeFunctorPost_isQCatEquivalence_on_base {A E F B D : SSet.{u}}
    [Quasicategory D] (p : E ⟶ B) (q : F ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (f : E ⟶ F) (hf : f ≫ q = p)
    (k : D ⟶ B)
    (h : ∀ d : D _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (k.app (Opposite.op ⦋0⦌) d))) (a : A ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf (a ≫ k)) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p k) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd q k) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd q k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q))⟩
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanIsPrecompositionEquivalence_of_leftFibration_fibers
    (pullback.snd p k) (pullback.snd q k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection p q f hf k) (by
      intro d
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso q k d)).isQCatEquivalence.cancel_right
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso q k d).hom)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_fiber]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso p k d)).isQCatEquivalence.comp (h d))
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    (pullback.snd p k) (pullback.snd q k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection p q f hf k) he a
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso q k a).hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso q k a)).isQCatEquivalence
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p k a).hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p k a)).isQCatEquivalence
  apply hu.cancel_left
  rw [← relativeFunctorBaseChangeForward_post p q f hf k a]
  exact hs.comp ht

/-- 局所対象だけを頂点に持つ任意の coherent 図式への切断では、指定辺の前合成が同値。 -/
lemma localDiagram_coslicePrecomposition_isQCatEquivalence
    {K X : SSet.{u}} [Quasicategory X] (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv e ∈ W)
    (a b : (Δ[0] : SSet.{u}) ⟶ X)
    (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a) (hb : stdSimplex.δ (0 : Fin 2) ≫ e = b)
    (D : K ⟶ X) (hD : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W (D.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgePrecompositionAt e a b ha hb)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgePrecompositionAt_projection e a b ha hb) D) := by
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W
  let D' : K ⟶ (L : SSet.{u}) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W) D hD
  have hDi : D' ≫ L.ι = D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have h := relativeFunctorPost_isQCatEquivalence_on_base
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgePrecompositionAt e a b ha hb)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgePrecompositionAt_projection e a b ha hb) L.ι (by
      intro z
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_edge_iff_coslicePrecomposition e a b ha hb _).mp
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isLocalForHom_homMk_iff_edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge e) _).mpr
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex z _ he) D'
  rwa [hDi] at h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
