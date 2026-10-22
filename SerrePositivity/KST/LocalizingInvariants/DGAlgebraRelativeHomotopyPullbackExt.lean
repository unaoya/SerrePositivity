module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeHomotopyPullbackLift

/-!
概要：相対経路模型の射は、元の二脚と全経路で一意に決まる。
方針：三段の実 pullback の共同単射性を使い、相対底を source から回収する。
規約：両端だけで一意性を主張しない。使われ方：class 経路による実同型の両逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeHomotopyPullback
variable (R : Type u) [CommRing R] {C B W D T : Mon (Complex R)}
  (p : C ⟶ B) (a : W ⟶ C) (g : D ⟶ C)

lemma hom_ext {u v : T ⟶ algebra R p a g}
    (hl : u ≫ left R p a g = v ≫ left R p a g)
    (hr : u ≫ right R p a g = v ≫ right R p a g)
    (hp : u ≫ path R p a g = v ≫ path R p a g) : u = v := by
  apply MonoidPullback.hom_ext (RelativeMappingPath.target R p a) g
  · apply MonoidPullback.hom_ext (RelativePath.source R p) a
    · apply MonoidPullback.hom_ext (Path.map R p) (Path.diagonal R B)
      · simpa only [path, RelativeMappingPath.inclusion, RelativePath.inclusion,
          Category.assoc] using hp
      · have hb : RelativePath.projection R p =
            RelativePath.inclusion R p ≫ Path.source R C ≫ p :=
          (RelativePath.source_projection R p).symm
        have hb' : MonoidPullback.snd (Path.map R p) (Path.diagonal R B) =
            MonoidPullback.fst (Path.map R p) (Path.diagonal R B) ≫ Path.source R C ≫ p := by
          simpa only [RelativePath.projection, RelativePath.inclusion] using hb
        simpa only [hb', path, RelativeMappingPath.inclusion, RelativePath.inclusion,
          Category.assoc] using
          congrArg (fun t => t ≫ Path.source R C ≫ p) hp
    · simpa only [left, RelativeMappingPath.projection, Category.assoc] using hl
  · exact hr

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeHomotopyPullback
