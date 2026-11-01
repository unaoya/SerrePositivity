module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverStars

/-!
# 元の根付き quiver の costar の持ち上げ

概要：指定した持ち上げ頂点へ入る元の矢も一意に持ち上がる。
方針：元の groupoid の逆射による右合成と元の逆射の法則を使う。
規約：元の基底矢と持ち上げ始点そのものを回収する。
使われ方：元の quiver の被覆性と対称化の一意な持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def backwardSource (x : Vertex A) {B : Q} (f : B ⟶ x.base) : Vertex A :=
  ⟨B, x.path ≫ inv ((Quiver.FreeGroupoid.of Q).map f)⟩

def backwardArrow (x : Vertex A) {B : Q} (f : B ⟶ x.base) :
    letI := quiver A
    backwardSource A x f ⟶ x := by
  letI := quiver A
  exact ⟨f, by simp only [backwardSource, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

def costarEquiv (x : Vertex A) :
    letI := quiver A
    Quiver.Costar x ≃ Quiver.Costar x.base := by
  letI := quiver A
  exact
    { toFun := fun s => ⟨s.1.base, s.2.val⟩
      invFun := fun s => ⟨backwardSource A x s.2, backwardArrow A x s.2⟩
      left_inv := by
        rintro ⟨⟨B, p⟩, ⟨f, hf⟩⟩
        change B ⟶ x.base at f
        change p ≫ (Quiver.FreeGroupoid.of Q).map f = x.path at hf
        have he := congrArg (fun q => q ≫ inv ((Quiver.FreeGroupoid.of Q).map f)) hf
        have hp : p = x.path ≫ inv ((Quiver.FreeGroupoid.of Q).map f) := by
          simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using he
        subst p
        rfl
      right_inv := by
        rintro ⟨B, f⟩
        rfl }

lemma projection_isCovering : letI := quiver A; (projection A).IsCovering := by
  let := quiver A
  exact ⟨star_bijective A, fun x => (costarEquiv A x).bijective⟩

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
