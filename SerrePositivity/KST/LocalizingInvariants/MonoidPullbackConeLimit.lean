module

public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal

/-!
概要：実代数射の四角形が underlying 圏で pullback なら、実代数圏でも pullback。
方針：元の複体の普遍性で持ち上げ、両射影の共同単射性で単位・積保存を証明する。
規約：tensor の極限保存を仮定しない。使われ方：Postnikov の元の上段を保つ普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants.MonoidPullback
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {W A B T : Mon C} (f : A ⟶ T) (g : B ⟶ T) (a : W ⟶ A) (b : W ⟶ B)
  (h : a ≫ f = b ≫ g)

include h in
lemma coneCondition_hom : a.hom ≫ f.hom = b.hom ≫ g.hom := congrArg Mon.Hom.hom h

variable (hl : IsLimit (PullbackCone.mk a.hom b.hom (coneCondition_hom f g a b h)))

def coneLiftHom (s : PullbackCone f g) : s.pt.X ⟶ W.X :=
  PullbackCone.IsLimit.lift hl s.fst.hom s.snd.hom (coneCondition_hom f g s.fst s.snd s.condition)

@[reassoc] lemma coneLiftHom_a (s : PullbackCone f g) : coneLiftHom f g a b h hl s ≫ a.hom =
    s.fst.hom := PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc] lemma coneLiftHom_b (s : PullbackCone f g) : coneLiftHom f g a b h hl s ≫ b.hom =
    s.snd.hom := PullbackCone.IsLimit.lift_snd _ _ _ _

lemma coneLiftHom_one (s : PullbackCone f g) :
    η[s.pt.X] ≫ coneLiftHom f g a b h hl s = η[W.X] := by
  apply PullbackCone.IsLimit.hom_ext hl
  · change (η[s.pt.X] ≫ coneLiftHom f g a b h hl s) ≫ a.hom = η[W.X] ≫ a.hom
    rw [Category.assoc, coneLiftHom_a, IsMonHom.one_hom, IsMonHom.one_hom]
  · change (η[s.pt.X] ≫ coneLiftHom f g a b h hl s) ≫ b.hom = η[W.X] ≫ b.hom
    rw [Category.assoc, coneLiftHom_b, IsMonHom.one_hom, IsMonHom.one_hom]

lemma coneLiftHom_mul (s : PullbackCone f g) :
    μ[s.pt.X] ≫ coneLiftHom f g a b h hl s =
      (coneLiftHom f g a b h hl s ⊗ₘ coneLiftHom f g a b h hl s) ≫ μ[W.X] := by
  apply PullbackCone.IsLimit.hom_ext hl
  · change (μ[s.pt.X] ≫ coneLiftHom f g a b h hl s) ≫ a.hom =
      ((coneLiftHom f g a b h hl s ⊗ₘ coneLiftHom f g a b h hl s) ≫ μ[W.X]) ≫ a.hom
    rw [Category.assoc, coneLiftHom_a, Category.assoc, IsMonHom.mul_hom a.hom,
      ← Category.assoc, tensorHom_comp_tensorHom, coneLiftHom_a]
    exact IsMonHom.mul_hom s.fst.hom
  · change (μ[s.pt.X] ≫ coneLiftHom f g a b h hl s) ≫ b.hom =
      ((coneLiftHom f g a b h hl s ⊗ₘ coneLiftHom f g a b h hl s) ≫ μ[W.X]) ≫ b.hom
    rw [Category.assoc, coneLiftHom_b, Category.assoc, IsMonHom.mul_hom b.hom,
      ← Category.assoc, tensorHom_comp_tensorHom, coneLiftHom_b]
    exact IsMonHom.mul_hom s.snd.hom

def coneLift (s : PullbackCone f g) : s.pt ⟶ W :=
  Mon.Hom.mk' (coneLiftHom f g a b h hl s) (coneLiftHom_one f g a b h hl s)
    (coneLiftHom_mul f g a b h hl s)

lemma coneLift_a (s : PullbackCone f g) : coneLift f g a b h hl s ≫ a = s.fst := by
  apply Mon.Hom.ext
  exact coneLiftHom_a f g a b h hl s

lemma coneLift_b (s : PullbackCone f g) : coneLift f g a b h hl s ≫ b = s.snd := by
  apply Mon.Hom.ext
  exact coneLiftHom_b f g a b h hl s

def isLimit_of_underlying : IsLimit (PullbackCone.mk a b h) :=
  PullbackCone.IsLimit.mk h (coneLift f g a b h hl) (coneLift_a f g a b h hl)
    (coneLift_b f g a b h hl) (fun s m ha hb => by
      apply Mon.Hom.ext
      apply PullbackCone.IsLimit.hom_ext hl
      · exact (congrArg Mon.Hom.hom ha).trans (coneLiftHom_a f g a b h hl s).symm
      · exact (congrArg Mon.Hom.hom hb).trans (coneLiftHom_b f g a b h hl s).symm)

end SerrePositivity.KST.LocalizingInvariants.MonoidPullback
