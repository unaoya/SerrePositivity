module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverStarAction

/-!
# 元の被覆の自由 groupoid の関手の忠実性

概要：射影が等しい元の二つの持ち上げ射は等しい。
方針：置換表現を始点の恒等射に作用させ、元の射を回収する。
規約：正向き射列の忠実性とは別に逆射を含む全射を扱う。
使われ方：元の根付き被覆の自由 groupoid の薄さ。

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

lemma groupoidProjection_faithful : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A; (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidProjection A).Faithful := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  refine ⟨?_⟩
  intro x y f g h
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A x f = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A x g :=
    congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.permutationRepresentation A x).map) h
  have he := congrArg
    (fun σ : Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LiftStar A x) => σ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A x x (𝟙 x))) hp
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A x f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A x x (𝟙 x)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A x y f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starRepresentation_action A x f (𝟙 x)).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A x y) (Category.id_comp f))
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A x g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A x x (𝟙 x)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A x y g :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starRepresentation_action A x g (𝟙 x)).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A x y) (Category.id_comp g))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar_injective A x y (hf.symm.trans (he.trans hg))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
