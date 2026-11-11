module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftEndpoint

/-!
# 指定した両端の間の射列の持ち上げ

概要：端点のラベルが整合する基底射列を実際の両端の間へ一意に持ち上げる。
方針：始点からの持ち上げの終点を同定して移送する。
規約：基底の正向き射列をそのまま回収する。
使われ方：元の hammock の全横射と縦射の持ち上げ。

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

def liftPathTo (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (p : Quiver.Path x.base y.base)
    (h : x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map p = y.path) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.Path x y := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_endpoint A x y p h ▸ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths.liftPath A x p).2

lemma pathStar_transport (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (q : Quiver.PathStar x) {y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A} (h : q.1 = y),
      (⟨y, h ▸ q.2⟩ : Quiver.PathStar x) = q := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  rintro ⟨y, q⟩ z h
  cases h
  rfl

lemma liftPathTo_star (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (p : Quiver.Path x.base y.base)
    (h : x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map p = y.path) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (⟨y, liftPathTo A x y p h⟩ : Quiver.PathStar x) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths.liftPath A x p := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact pathStar_transport A x _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_endpoint A x y p h)

lemma liftPathTo_projection (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (p : Quiver.Path x.base y.base)
    (h : x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map p = y.path) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).mapPath (liftPathTo A x y p h) = p := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  have he := (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).pathStar x) (liftPathTo_star A x y p h)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths.liftPath_projection A x p)
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

lemma liftPathTo_unique (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (p : Quiver.Path x.base y.base)
    (h : x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map p = y.path) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ q : Quiver.Path x y, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).mapPath q = p → q = liftPathTo A x y p h := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro q hq
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths.lifted_pathStar_unique A x (⟨y, q⟩ : Quiver.PathStar x)
    ⟨y, liftPathTo A x y p h⟩
    (congrArg (Sigma.mk y.base) (hq.trans (liftPathTo_projection A x y p h).symm))
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

lemma existsUnique_liftPathTo (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (p : Quiver.Path x.base y.base)
    (h : x.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map p = y.path) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∃! q : Quiver.Path x y, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).mapPath q = p := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact ⟨liftPathTo A x y p h, liftPathTo_projection A x y p h,
    fun q hq => liftPathTo_unique A x y p h q hq⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
