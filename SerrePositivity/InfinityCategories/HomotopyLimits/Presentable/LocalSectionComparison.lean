module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Fibrations.BaseChange
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChangeNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostEquivalence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberComparisonBaseChange
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexFiberBaseChange
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalCoslicePrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalObjects
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFiberPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeCosliceIntervalMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectiveInvertedHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeFunctorPostcomposition

/-!
概要：局所対象の図式への表現可能 left fibration の切断の比較。
方針：局所対象の全部分圏へ底変換し、fiber ごとの同値を切断へ移す。
規約：図式の添字には quasicategory 性を要求しない。
使われ方：HTT 5.5.4 の局所対象の極限閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 相対切断の底変換は、元の底上の射による後合成と厳密に可換。 -/
lemma relativeFunctorBaseChangeForward_post {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (k : D ⟶ B) (a : A ⟶ D) :
    relativeFunctorPost (pullback.snd p k) (pullback.snd q k)
        (SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange p q f hf k)
        (SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange_projection p q f hf k) a ≫
      (relativeFunctorBaseChangeIso q k a).hom =
    (relativeFunctorBaseChangeIso p k a).hom ≫ relativeFunctorPost p q f hf (a ≫ k) := by
  apply vertexFiber_hom_ext ((ihom A).map q) (functorVertex (a ≫ k))
  change (_ ≫ relativeFunctorBaseChangeForward q k a) ≫ _ =
    (relativeFunctorBaseChangeForward p k a ≫ _) ≫ _
  rw [Category.assoc, relativeFunctorBaseChangeForward_ι, ← Category.assoc,
    relativeFunctorPost_ι, Category.assoc, Category.assoc, relativeFunctorPost_ι,
    ← Category.assoc]
  conv_rhs => rw [← Category.assoc, relativeFunctorBaseChangeForward_ι]
  simp only [Category.assoc, ← Functor.map_comp,
    SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange, pullback.lift_fst]

/-- 同値な fiber を持つ部分圏へ着地する任意の図式では、相対切断の後合成が同値。 -/
lemma relativeFunctorPost_isQCatEquivalence_on_base {A E F B D : SSet.{u}}
    [Quasicategory D] (p : E ⟶ B) (q : F ⟶ B)
    [LeftFibration p] [LeftFibration q] (f : E ⟶ F) (hf : f ≫ q = p)
    (k : D ⟶ B)
    (h : ∀ d : D _⦋0⦌, IsQCatEquivalence
      (vertexFiberMap p q f hf (k.app (Opposite.op ⦋0⦌) d))) (a : A ⟶ D) :
    IsQCatEquivalence (relativeFunctorPost p q f hf (a ≫ k)) := by
  have : LeftFibration (pullback.snd p k) :=
    ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩
  have : LeftFibration (pullback.snd q k) :=
    ⟨leftFibrations.pullback_snd q k (LeftFibration.mem (p := q))⟩
  have he := F1B.kanIsPrecompositionEquivalence_of_leftFibration_fibers
    (pullback.snd p k) (pullback.snd q k)
    (SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange p q f hf k)
    (SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange_projection p q f hf k) (by
      intro d
      apply (qCatEquivalenceOfIso
        (cofinalVertexFiberBaseChangeIso q k d)).isQCatEquivalence.cancel_right
      change IsQCatEquivalence (_ ≫ (cofinalVertexFiberBaseChangeIso q k d).hom)
      rw [SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange_fiber]
      exact (qCatEquivalenceOfIso
        (cofinalVertexFiberBaseChangeIso p k d)).isQCatEquivalence.comp (h d))
  have hs := relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    (pullback.snd p k) (pullback.snd q k)
    (SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange p q f hf k)
    (SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange_projection p q f hf k) he a
  have ht : IsQCatEquivalence (relativeFunctorBaseChangeIso q k a).hom :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso q k a)).isQCatEquivalence
  have hu : IsQCatEquivalence (relativeFunctorBaseChangeIso p k a).hom :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso p k a)).isQCatEquivalence
  apply hu.cancel_left
  rw [← relativeFunctorBaseChangeForward_post p q f hf k a]
  exact hs.comp ht

/-- 局所対象だけを頂点に持つ任意の coherent 図式への切断では、指定辺の前合成が同値。 -/
lemma localDiagram_coslicePrecomposition_isQCatEquivalence
    {K X : SSet.{u}} [Quasicategory X] (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv e ∈ W)
    (a b : (Δ[0] : SSet.{u}) ⟶ X)
    (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a) (hb : stdSimplex.δ (0 : Fin 2) ≫ e = b)
    (D : K ⟶ X) (hD : ∀ k : K _⦋0⦌, IsLocalObject W (D.app (Opposite.op ⦋0⦌) k)) :
    IsQCatEquivalence (relativeFunctorPost (sliceUnderProjection b) (sliceUnderProjection a)
      (cosliceEdgePrecompositionAt e a b ha hb)
      (cosliceEdgePrecompositionAt_projection e a b ha hb) D) := by
  let L := localObjectsSubcomplex W
  let D' : K ⟶ (L : SSet.{u}) := fullSubcomplexLift (IsLocalObject W) D hD
  have hDi : D' ≫ L.ι = D := fullSubcomplexLift_ι _ _ _
  have h := relativeFunctorPost_isQCatEquivalence_on_base
    (sliceUnderProjection b) (sliceUnderProjection a)
    (cosliceEdgePrecompositionAt e a b ha hb)
    (cosliceEdgePrecompositionAt_projection e a b ha hb) L.ι (by
      intro z
      apply (isLocalForHom_edge_iff_coslicePrecomposition e a b ha hb _).mp
      apply (isLocalForHom_homMk_iff_edgeOfSimplex (edgeCosliceEdge e) _).mpr
      exact fullSubcomplexOnVertices_vertex z _ he) D'
  rwa [hDi] at h

end SerrePositivity.InfinityCategories.HomotopyLimits
