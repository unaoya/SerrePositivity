module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverStarAction

/-!
# 元の被覆の自由 groupoid の関手の忠実性

概要：射影が等しい元の二つの持ち上げ射は等しい。
方針：置換表現を始点の恒等射に作用させ、元の射を回収する。
規約：正向き射列の忠実性とは別に逆射を含む全射を扱う。
使われ方：元の根付き被覆の自由 groupoid の薄さ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma groupoidProjection_faithful : letI := quiver A; (groupoidProjection A).Faithful := by
  let := quiver A
  refine ⟨?_⟩
  intro x y f g h
  have hp : starPermutation A x f = starPermutation A x g :=
    congrArg ((permutationRepresentation A x).map) h
  have he := congrArg
    (fun σ : Equiv.Perm (LiftStar A x) => σ (encodeStar A x x (𝟙 x))) hp
  have hf : starPermutation A x f (encodeStar A x x (𝟙 x)) = encodeStar A x y f :=
    (starRepresentation_action A x f (𝟙 x)).trans
      (congrArg (encodeStar A x y) (Category.id_comp f))
  have hg : starPermutation A x g (encodeStar A x x (𝟙 x)) = encodeStar A x y g :=
    (starRepresentation_action A x g (𝟙 x)).trans
      (congrArg (encodeStar A x y) (Category.id_comp g))
  exact encodeStar_injective A x y (hf.symm.trans (he.trans hg))

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
