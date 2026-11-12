module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFaithful

/-!
# 元の根付き被覆の自由 groupoid 間の射影

概要：元の被覆の quiver 射影を元の自由 groupoid の関手へ移す。
方針：元の自由 groupoid の関手性と元の生成矢の像を使う。
規約：正向き射列の忠実性を groupoid の忠実性として使わない。
使われ方：根付き被覆の木性と元の逆対の持ち上げ。

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

def groupoidProjection :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) ⥤ Quiver.FreeGroupoid Q := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact Quiver.freeGroupoidFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A)

lemma groupoidProjection_generator (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ f : x ⟶ y,
      (groupoidProjection A).map ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f) =
        (Quiver.FreeGroupoid.of Q).map f.val := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro f
  rfl

lemma groupoidProjection_endpoint :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ {x y : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)} (f : x ⟶ y),
      x.as.path ≫ (groupoidProjection A).map f = y.as.path := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro x y f
  induction f using Quiver.FreeGroupoid.hom_rec with
  | of_map f =>
    rw [groupoidProjection_generator]
    exact f.property
  | @inv_of_map x y f =>
    let e := (Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f
    have hg : x.path ≫ (groupoidProjection A).map e = y.path := by
      rw [groupoidProjection_generator]
      exact f.property
    have he := congrArg (fun p => p ≫ inv ((groupoidProjection A).map e)) hg
    have hp : x.path = y.path ≫ inv ((groupoidProjection A).map e) := by
      simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using he
    exact (congrArg (fun p => y.path ≫ p) ((groupoidProjection A).map_inv e)).trans hp.symm
  | id x =>
    exact (congrArg (fun p => x.path ≫ p) ((groupoidProjection A).map_id _)).trans
      (Category.comp_id x.path)
  | comp f g ihf ihg =>
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ihf]
    exact ihg

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
