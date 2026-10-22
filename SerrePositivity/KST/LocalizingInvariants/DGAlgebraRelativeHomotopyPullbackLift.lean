module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeHomotopyPullback

/-!
概要：指定された底上の乗法的経路を、相対 homotopy-pullback 模型へ実代数射で持ち上げる。
方針：相対経路、相対 mapping-path、最後の pullback の三つの普遍性を順に使う。
規約：元の二脚と全経路を保持。使われ方：相対 class 経路による模型の移送。
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
  (p : C ⟶ B) (a : W ⟶ C) (g : D ⟶ C) (l : T ⟶ W) (r : T ⟶ D)
  (v : Path.Witness R (l ≫ a) (r ≫ g))
  (hp : v.hom ≫ Path.map R p = (l ≫ a ≫ p) ≫ Path.diagonal R B)

def liftPath : T ⟶ RelativePath.algebra R p :=
  MonoidPullback.lift (Path.map R p) (Path.diagonal R B) v.hom (l ≫ a ≫ p) hp

lemma liftPath_inclusion : liftPath R p a g l r v hp ≫ RelativePath.inclusion R p = v.hom :=
  MonoidPullback.lift_fst _ _ _ _ _

lemma liftPath_source : liftPath R p a g l r v hp ≫ RelativePath.source R p = l ≫ a := by
  rw [RelativePath.source, ← Category.assoc, liftPath_inclusion, v.source_eq]

lemma liftPath_target : liftPath R p a g l r v hp ≫ RelativePath.target R p = r ≫ g := by
  rw [RelativePath.target, ← Category.assoc, liftPath_inclusion, v.target_eq]

def liftMappingPath : T ⟶ RelativeMappingPath.algebra R p a :=
  MonoidPullback.lift (RelativePath.source R p) a (liftPath R p a g l r v hp) l
    (liftPath_source R p a g l r v hp)

lemma liftMappingPath_projection :
    liftMappingPath R p a g l r v hp ≫ RelativeMappingPath.projection R p a = l :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma liftMappingPath_inclusion :
    liftMappingPath R p a g l r v hp ≫ RelativeMappingPath.inclusion R p a =
      liftPath R p a g l r v hp := MonoidPullback.lift_fst _ _ _ _ _

lemma liftMappingPath_target :
    liftMappingPath R p a g l r v hp ≫ RelativeMappingPath.target R p a = r ≫ g := by
  rw [RelativeMappingPath.target, ← Category.assoc, liftMappingPath_inclusion, liftPath_target]

def lift : T ⟶ algebra R p a g :=
  MonoidPullback.lift (RelativeMappingPath.target R p a) g
    (liftMappingPath R p a g l r v hp) r (liftMappingPath_target R p a g l r v hp)

lemma lift_left : lift R p a g l r v hp ≫ left R p a g = l := by
  rw [left, ← Category.assoc]
  change (MonoidPullback.lift _ _ _ _ _ ≫ MonoidPullback.fst _ _) ≫ _ = _
  rw [MonoidPullback.lift_fst, liftMappingPath_projection]

lemma lift_right : lift R p a g l r v hp ≫ right R p a g = r :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma lift_path : lift R p a g l r v hp ≫ path R p a g = v.hom := by
  rw [path, ← Category.assoc]
  change (MonoidPullback.lift _ _ _ _ _ ≫ MonoidPullback.fst _ _) ≫ _ = _
  rw [MonoidPullback.lift_fst, ← Category.assoc, liftMappingPath_inclusion, liftPath_inclusion]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeHomotopyPullback
