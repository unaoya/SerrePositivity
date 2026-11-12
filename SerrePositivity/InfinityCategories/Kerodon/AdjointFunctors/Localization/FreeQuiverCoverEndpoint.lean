module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation

/-!
# 元の対称化した持ち上げ射列の終点の回収

概要：持ち上げた射列の終点の groupoid の矢は始点の矢と元の射列の値の合成である。
方針：元の正向き・逆向きの矢の等式を元の射列の長さで反復する。
規約：実際の持ち上げ終点と元の商の矢を回収する。
使われ方：根からの連結性と元の hammock の固定端点の持ち上げ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma coverEvaluation_arrow (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ f : @Quiver.Hom (Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))
        (@Quiver.symmetrifyQuiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A)) x y,
      x.path ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.coverEvaluation A).map f.toPath = y.path := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro f
  change (x ⟶ y) ⊕ (y ⟶ x) at f
  cases f with
  | inl f =>
    change x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.symmetricEvaluation.map f.val.toPosPath = y.path
    exact f.property
  | inr f =>
    change x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.symmetricEvaluation.map f.val.toNegPath = y.path
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.evaluation_negative]
    have he := congrArg (fun p => p ≫ inv ((Quiver.FreeGroupoid.of Q).map f.val)) f.property
    have hp : y.path = x.path ≫ inv ((Quiver.FreeGroupoid.of Q).map f.val) := by
      simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using he
    exact hp.symm

lemma coverEvaluation_endpoint (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ p : @Quiver.Path (Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))
        (@Quiver.symmetrifyQuiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A)) x y,
      x.path ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.coverEvaluation A).map p = y.path := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro p
  induction p with
  | nil =>
    change x.path ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.coverEvaluation A).map (𝟙 _) = x.path
    exact (congrArg (fun q => x.path ≫ q) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.coverEvaluation A).map_id x)).trans
      (Category.comp_id x.path)
  | @cons y z p f ih =>
    have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.coverEvaluation A).map
        (@Quiver.Path.cons (Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))
          (@Quiver.symmetrifyQuiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A)) x y z p f) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.coverEvaluation A).map p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.coverEvaluation A).map
          (@Quiver.Hom.toPath (Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))
            (@Quiver.symmetrifyQuiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A)) y z f) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.coverEvaluation A).map_comp p
        (@Quiver.Hom.toPath (Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))
          (@Quiver.symmetrifyQuiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A)) y z f)
    rw [hc, ← Category.assoc, ih]
    exact coverEvaluation_arrow A y z f

lemma projected_endpoint (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ p : @Quiver.Path (Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))
        (@Quiver.symmetrifyQuiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A)) x y,
      x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.symmetricEvaluation.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.symmetricProjection A).mapPath p) = y.path := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro p
  exact coverEvaluation_endpoint A x y p

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
