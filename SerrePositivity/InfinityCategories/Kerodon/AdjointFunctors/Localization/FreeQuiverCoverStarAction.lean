module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverPermutationRepresentation

/-!
# 元の置換表現による全持ち上げ射の回収

概要：射影した元の groupoid の射の置換作用は同じ持ち上げ射の右合成を回収する。
方針：元の生成矢・逆生成矢・単位・合成で帰納する。
規約：元の持ち上げ射を回収し、忠実性を仮定しない。
使われ方：元の自由 groupoid 間の射影の忠実性。

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

lemma starRepresentation_generator_inverse :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A} (f : x ⟶ y),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A S (inv ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorPermutation A S f.val).symm := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S x y f
  calc
    _ = inv ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starRepresentation A S).map ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f)) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starRepresentation A S).map_inv _
    _ = (show Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LiftStar A S) from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starRepresentation A S).map ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f))⁻¹ :=
      SingleObj.inv_as_inv _ _
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starRepresentation_generator]; rfl

lemma starRepresentation_action :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) {x y : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)} (f : x ⟶ y)
      (h : S ⟶ x), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A S f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S x h) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S y (h ≫ f) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S x y f
  induction f using Quiver.FreeGroupoid.hom_rec with
  | of_map f =>
    intro h
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorPermutation A S f.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S _ h) = _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorPermutation_forward A S f h
  | inv_of_map f =>
    intro h
    rw [starRepresentation_generator_inverse]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorPermutation_backward A S f h
  | id x =>
    intro h
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A S (𝟙 ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj x)) = 1 :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starRepresentation A S).map_id _
    rw [hi]
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S _) (Category.comp_id h)).symm
  | comp f g ihf ihg =>
    intro h
    have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A S (f ≫ g) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A S g * _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A S f :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starRepresentation A S).map_comp f g
    rw [hc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A S g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.starPermutation A S f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S _ h)) = _
    rw [ihf, ihg]
    exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S _) (Category.assoc h f g)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
