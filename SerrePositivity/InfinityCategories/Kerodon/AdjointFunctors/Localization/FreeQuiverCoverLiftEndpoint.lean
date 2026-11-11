module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFaithful

/-!
# 指定始点からの射列の持ち上げ終点

概要：元の基底射列の値から実際の持ち上げ終点を回収する。
方針：pathStar の像の等式から基底頂点と射列を回収し、終点の式を使う。
規約：終点の頂点そのものを同定する。
使われ方：指定した両端の間の射列の一意な持ち上げ。

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

lemma pathStar_endpoint (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ q : Quiver.PathStar x, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).pathStar x q = ⟨B, p⟩ →
      q.1 = (⟨B, x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map p⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  rintro ⟨⟨E, γ⟩, q⟩ h
  obtain ⟨hb, hp⟩ := Sigma.mk.inj_iff.mp h
  change E = B at hb
  subst B
  have hpath : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).mapPath q = p := eq_of_heq hp
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positive_endpoint A x (⟨E, γ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) q
  rw [hpath] at he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Vertex.ext rfl (heq_of_eq he.symm)

lemma liftPath_endpoint (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths.liftPath A x p).1 = (⟨B, x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map p⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact pathStar_endpoint A x p _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths.liftPath_projection A x p)

lemma liftPathTo_endpoint (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (p : Quiver.Path x.base y.base)
    (h : x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map p = y.path) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths.liftPath A x p).1 = y := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact (liftPath_endpoint A x p).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Vertex.ext rfl (heq_of_eq h))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
