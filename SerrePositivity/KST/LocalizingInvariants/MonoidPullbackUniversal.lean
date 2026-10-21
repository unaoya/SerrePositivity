module

public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackStructure

/-!
概要：構成した実モノイド対象の pullback の、代数射に対する普遍性。
方針：複体側の持ち上げに単位と積保存を与え、両射影の共同単射性で一意性を示す。
規約：モノイド対象圏の極限の存在を入力にしない。使われ方：実相対経路代数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants.MonoidPullback
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B D : Mon C} (f : A ⟶ D) (g : B ⟶ D) [HasPullback f.hom g.hom]
  {W : Mon C} (a : W ⟶ A) (b : W ⟶ B) (h : a ≫ f = b ≫ g)

include h in
lemma liftHom_one : η[W.X] ≫ pullback.lift a.hom b.hom (congrArg Mon.Hom.hom h) = one f g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, IsMonHom.one_hom, one_fst]
  · rw [Category.assoc, pullback.lift_snd, IsMonHom.one_hom, one_snd]

include h in
lemma liftHom_mul :
    μ[W.X] ≫ pullback.lift a.hom b.hom (congrArg Mon.Hom.hom h) =
      (pullback.lift a.hom b.hom (congrArg Mon.Hom.hom h) ⊗ₘ
        pullback.lift a.hom b.hom (congrArg Mon.Hom.hom h)) ≫ mul f g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, mul_fst,
      ← Category.assoc, tensorHom_comp_tensorHom, pullback.lift_fst]
    exact IsMonHom.mul_hom a.hom
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, mul_snd,
      ← Category.assoc, tensorHom_comp_tensorHom, pullback.lift_snd]
    exact IsMonHom.mul_hom b.hom

def lift : W ⟶ obj f g :=
  Mon.Hom.mk' (pullback.lift a.hom b.hom (congrArg Mon.Hom.hom h))
    (liftHom_one f g a b h) (liftHom_mul f g a b h)

@[reassoc]
lemma lift_fst : lift f g a b h ≫ fst f g = a := by
  apply Mon.Hom.ext
  exact pullback.lift_fst _ _ _

@[reassoc]
lemma lift_snd : lift f g a b h ≫ snd f g = b := by
  apply Mon.Hom.ext
  exact pullback.lift_snd _ _ _

lemma hom_ext {a b : W ⟶ obj f g}
    (ha : a ≫ fst f g = b ≫ fst f g) (hb : a ≫ snd f g = b ≫ snd f g) : a = b := by
  apply Mon.Hom.ext
  exact pullback.hom_ext (congrArg Mon.Hom.hom ha) (congrArg Mon.Hom.hom hb)

def cone : PullbackCone f g := PullbackCone.mk (fst f g) (snd f g) (condition f g)

def isLimit : IsLimit (cone f g) :=
  PullbackCone.IsLimit.mk (condition f g)
    (fun s => lift f g s.fst s.snd s.condition)
    (fun s => lift_fst f g s.fst s.snd s.condition)
    (fun s => lift_snd f g s.fst s.snd s.condition)
    (fun s _m ha hb => hom_ext f g (ha.trans (lift_fst f g _ _ _).symm)
      (hb.trans (lift_snd f g _ _ _).symm))

lemma hasPullback : HasPullback f g := ⟨⟨⟨cone f g, isLimit f g⟩⟩⟩

end SerrePositivity.KST.LocalizingInvariants.MonoidPullback
