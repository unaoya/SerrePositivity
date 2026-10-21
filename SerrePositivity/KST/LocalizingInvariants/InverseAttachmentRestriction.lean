module

public import SerrePositivity.KST.LocalizingInvariants.InverseAttachment

/-!
概要：辺反転の貼合せからの制限と、元の各指定辺への制限を厳密に照合する。
方針：反転関手の頂点条件で各辺の制限を可逆 path へ持ち上げ、貼合せ等式を使う。
規約：元の辺・元の制限写像を保持。使われ方：一般商の全関手圏での普遍性。
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
variable (X : SSet.{u}) (W : Set (X _⦋1⦌)) (Y : SSet.{u})

def invertingEdgeRestriction (w : W) :
    (invertingFunctors X Y W : SSet.{u}) ⟶ equivalencePath Y :=
  fullSubcomplexLift IsEquivalencePathVertex
    ((invertingFunctors X Y W).ι ≫ (pre (SSet.yonedaEquiv.symm w.val)).app Y) (by
      intro v
      have hv := fullSubcomplexOnVertices_vertex v
      change IsInvertingFunctorVertex X Y W v.val at hv
      obtain ⟨F, hF⟩ := (functorVertexEquiv X Y).surjective v.val
      rw [← hF] at hv
      change InvertsEdges F W at hv
      change IsEquivalencePathVertex
        (((pre (SSet.yonedaEquiv.symm w.val)).app Y).app (Opposite.op ⦋0⦌) v.val)
      rw [← hF]
      change IsEquivalencePathVertex (functorVertex (SSet.yonedaEquiv.symm w.val ≫ F))
      rw [IsEquivalencePathVertex, intervalFunctorVertexEdge_functorVertex,
        SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact (isInvertibleEdge_congr (e := (edgeOfSimplex w.val).map ((truncation 2).map F))
        (f := edgeOfSimplex (F.app (Opposite.op ⦋1⦌) w.val)) rfl).mp (hv w.property))

lemma invertingEdgeRestriction_ι (w : W) :
    invertingEdgeRestriction X W Y w ≫ equivalencePathι Y =
      (invertingFunctors X Y W).ι ≫ (pre (SSet.yonedaEquiv.symm w.val)).app Y :=
  fullSubcomplexLift_ι _ _ _

def inverseAttachmentRestriction : (ihom (inverseAttachment X W)).obj Y ⟶
    (invertingFunctors X Y W : SSet.{u}) :=
  localizationPrecomposition (inverseAttachmentInclusion X W) W (inverseAttachment_inverts X W) Y

lemma inverseAttachmentRestriction_ι :
    inverseAttachmentRestriction X W Y ≫ (invertingFunctors X Y W).ι =
      (pre (inverseAttachmentInclusion X W)).app Y := localizationPrecomposition_ι _ _ _ _

lemma inverseAttachmentRestriction_interval (w : W) :
    inverseAttachmentRestriction X W Y ≫ invertingEdgeRestriction X W Y w =
      (pre (inverseAttachmentInterval X W w)).app Y ≫ walkingEquivalenceRestriction Y := by
  have : Mono (equivalencePathι Y) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices _ IsEquivalencePathVertex).ι)
  apply (cancel_mono (equivalencePathι Y)).mp
  rw [Category.assoc, invertingEdgeRestriction_ι, ← Category.assoc,
    inverseAttachmentRestriction_ι, Category.assoc, walkingEquivalenceRestriction_ι]
  rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
    inverseAttachment_edge]

end SerrePositivity.KST.LocalizingInvariants
