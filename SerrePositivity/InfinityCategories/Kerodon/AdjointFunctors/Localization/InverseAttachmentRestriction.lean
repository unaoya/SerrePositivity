module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InverseAttachment

/-!
概要：辺反転の貼合せからの制限と、元の各指定辺への制限を厳密に照合する。
方針：反転関手の頂点条件で各辺の制限を可逆 path へ持ち上げ、貼合せ等式を使う。
規約：元の辺・元の制限写像を保持。使われ方：一般商の全関手圏での普遍性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (X : SSet.{u}) (W : Set (X _⦋1⦌)) (Y : SSet.{u})

def invertingEdgeRestriction (w : W) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι ≫ (pre (SSet.yonedaEquiv.symm w.val)).app Y) (by
      intro v
      have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X Y W v.val at hv
      obtain ⟨F, hF⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).surjective v.val
      rw [← hF] at hv
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W at hv
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
        (((pre (SSet.yonedaEquiv.symm w.val)).app Y).app (Opposite.op ⦋0⦌) v.val)
      rw [← hF]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm w.val ≫ F))
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex,
        SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex w.val).map ((truncation 2).map F))
        (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.app (Opposite.op ⦋1⦌) w.val)) rfl).mp (hv w.property))

lemma invertingEdgeRestriction_ι (w : W) :
    invertingEdgeRestriction X W Y w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι ≫ (pre (SSet.yonedaEquiv.symm w.val)).app Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

def inverseAttachmentRestriction : (ihom (inverseAttachment X W)).obj Y ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (inverseAttachmentInclusion X W) W (inverseAttachment_inverts X W) Y

lemma inverseAttachmentRestriction_ι :
    inverseAttachmentRestriction X W Y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι =
      (pre (inverseAttachmentInclusion X W)).app Y := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι _ _ _ _

lemma inverseAttachmentRestriction_interval (w : W) :
    inverseAttachmentRestriction X W Y ≫ invertingEdgeRestriction X W Y w =
      (pre (inverseAttachmentInterval X W w)).app Y ≫ walkingEquivalenceRestriction Y := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex).ι)
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)).mp
  rw [Category.assoc, invertingEdgeRestriction_ι, ← Category.assoc,
    inverseAttachmentRestriction_ι, Category.assoc, walkingEquivalenceRestriction_ι]
  rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
    inverseAttachment_edge]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
