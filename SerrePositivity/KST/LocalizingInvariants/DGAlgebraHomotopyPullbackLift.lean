module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackModel

/-!
概要：元の二脚と指定された実乗法的経路を、cospan 模型への実代数射へ持ち上げる。
方針：mapping-path と外側の実 pullback を順に使い、三成分から一意性を示す。
規約：任意の ∞ 錐の持ち上げを入力しない。使われ方：実拡大と模型の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B C W : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)
  (a : W ⟶ A) (b : W ⟶ C) (h : Path.Witness R (a ≫ f) (b ≫ g))

def liftReplacement : W ⟶ MappingPath.algebra R f :=
  MappingPath.lift R f h.hom a h.source_eq

lemma liftReplacement_target : liftReplacement R f g a b h ≫ MappingPath.target R f = b ≫ g :=
  (MappingPath.lift_target R f h.hom a h.source_eq).trans h.target_eq

def lift : W ⟶ algebra R f g := MonoidPullback.lift (MappingPath.target R f) g
  (liftReplacement R f g a b h) b (liftReplacement_target R f g a b h)

@[reassoc]
lemma lift_replacedProjection : lift R f g a b h ≫ replacedProjection R f g =
    liftReplacement R f g a b h := MonoidPullback.lift_fst _ _ _ _ _

@[reassoc]
lemma lift_right : lift R f g a b h ≫ right R f g = b := MonoidPullback.lift_snd _ _ _ _ _

@[reassoc]
lemma lift_left : lift R f g a b h ≫ left R f g = a := by
  change lift R f g a b h ≫ (replacedProjection R f g ≫ MappingPath.projection R f) = _
  rw [← Category.assoc, lift_replacedProjection]
  exact MappingPath.lift_projection R f h.hom a h.source_eq

@[reassoc]
lemma lift_path : lift R f g a b h ≫ path R f g = h.hom := by
  change lift R f g a b h ≫ (replacedProjection R f g ≫ MappingPath.inclusion R f) = _
  rw [← Category.assoc, lift_replacedProjection]
  exact MappingPath.lift_inclusion R f h.hom a h.source_eq

lemma hom_ext {u v : W ⟶ algebra R f g}
    (ha : u ≫ left R f g = v ≫ left R f g)
    (hb : u ≫ right R f g = v ≫ right R f g)
    (hp : u ≫ path R f g = v ≫ path R f g) : u = v := by
  apply MonoidPullback.hom_ext (MappingPath.target R f) g
  · change u ≫ replacedProjection R f g = v ≫ replacedProjection R f g
    apply MappingPath.hom_ext R f
    · change u ≫ (replacedProjection R f g ≫ MappingPath.inclusion R f) =
        v ≫ (replacedProjection R f g ≫ MappingPath.inclusion R f) at hp
      simpa only [Category.assoc] using hp
    · change u ≫ (replacedProjection R f g ≫ MappingPath.projection R f) =
        v ≫ (replacedProjection R f g ≫ MappingPath.projection R f) at ha
      simpa only [Category.assoc] using ha
  · exact hb

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
