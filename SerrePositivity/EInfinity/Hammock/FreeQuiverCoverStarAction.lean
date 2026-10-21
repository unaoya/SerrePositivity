module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverPermutationRepresentation

/-!
# 元の置換表現による全持ち上げ射の回収

概要：射影した元の groupoid の射の置換作用は同じ持ち上げ射の右合成を回収する。
方針：元の生成矢・逆生成矢・単位・合成で帰納する。
規約：元の持ち上げ射を回収し、忠実性を仮定しない。
使われ方：元の自由 groupoid 間の射影の忠実性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma starRepresentation_generator_inverse :
    letI := quiver A
    ∀ (S : Quiver.FreeGroupoid (Vertex A)) {x y : Vertex A} (f : x ⟶ y),
      starPermutation A S (inv ((Quiver.FreeGroupoid.of (Vertex A)).map f)) =
        (generatorPermutation A S f.val).symm := by
  let := quiver A
  intro S x y f
  calc
    _ = inv ((starRepresentation A S).map ((Quiver.FreeGroupoid.of (Vertex A)).map f)) :=
      (starRepresentation A S).map_inv _
    _ = (show Equiv.Perm (LiftStar A S) from
      (starRepresentation A S).map ((Quiver.FreeGroupoid.of (Vertex A)).map f))⁻¹ :=
      SingleObj.inv_as_inv _ _
    _ = _ := by rw [starRepresentation_generator]; rfl

lemma starRepresentation_action :
    letI := quiver A
    ∀ (S : Quiver.FreeGroupoid (Vertex A)) {x y : Quiver.FreeGroupoid (Vertex A)} (f : x ⟶ y)
      (h : S ⟶ x), starPermutation A S f (encodeStar A S x h) =
        encodeStar A S y (h ≫ f) := by
  let := quiver A
  intro S x y f
  induction f using Quiver.FreeGroupoid.hom_rec with
  | of_map f =>
    intro h
    change (generatorPermutation A S f.val) (encodeStar A S _ h) = _
    exact generatorPermutation_forward A S f h
  | inv_of_map f =>
    intro h
    rw [starRepresentation_generator_inverse]
    exact generatorPermutation_backward A S f h
  | id x =>
    intro h
    have hi : starPermutation A S (𝟙 ((Quiver.FreeGroupoid.of (Vertex A)).obj x)) = 1 :=
      (starRepresentation A S).map_id _
    rw [hi]
    exact (congrArg (encodeStar A S _) (Category.comp_id h)).symm
  | comp f g ihf ihg =>
    intro h
    have hc : starPermutation A S (f ≫ g) = starPermutation A S g * starPermutation A S f :=
      (starRepresentation A S).map_comp f g
    rw [hc]
    change starPermutation A S g (starPermutation A S f (encodeStar A S _ h)) = _
    rw [ihf, ihg]
    exact congrArg (encodeStar A S _) (Category.assoc h f g)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
