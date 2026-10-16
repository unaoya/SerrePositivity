module
public import SerrePositivity.DifferentialGraded.Module.HomWhisker

/-! # 全Hom可換四角形の恒等と合成 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

lemma moduleHom_square_id {K : Complex A} {X Y : ModuleCategory A B}
    (f : K ⟶ (X ⟶[Complex A] Y)) :
    f ≫ eHomWhiskerLeft (Complex A) X (𝟙 Y) =
      f ≫ eHomWhiskerRight (Complex A) (𝟙 X) Y := by simp

lemma moduleHom_square_comp {K : Complex A} {X₁ Y₁ X₂ Y₂ X₃ Y₃ : ModuleCategory A B}
    (f : K ⟶ (X₁ ⟶[Complex A] Y₁)) (g : K ⟶ (X₂ ⟶[Complex A] Y₂))
    (h : K ⟶ (X₃ ⟶[Complex A] Y₃))
    (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (a' : X₂ ⟶ X₃) (b' : Y₂ ⟶ Y₃)
    (wf : f ≫ eHomWhiskerLeft (Complex A) X₁ b =
      g ≫ eHomWhiskerRight (Complex A) a Y₂)
    (wg : g ≫ eHomWhiskerLeft (Complex A) X₂ b' =
      h ≫ eHomWhiskerRight (Complex A) a' Y₃) :
    f ≫ eHomWhiskerLeft (Complex A) X₁ (b ≫ b') =
      h ≫ eHomWhiskerRight (Complex A) (a ≫ a') Y₃ := by
  calc
    _ = (f ≫ eHomWhiskerLeft (Complex A) X₁ b) ≫
        eHomWhiskerLeft (Complex A) X₁ b' := by
      rw [eHomWhiskerLeft_comp, Category.assoc]
    _ = (g ≫ eHomWhiskerRight (Complex A) a Y₂) ≫
        eHomWhiskerLeft (Complex A) X₁ b' := by rw [wf]
    _ = (g ≫ eHomWhiskerLeft (Complex A) X₂ b') ≫
        eHomWhiskerRight (Complex A) a Y₃ := by
      rw [Category.assoc, Category.assoc, eHom_whisker_exchange]
    _ = (h ≫ eHomWhiskerRight (Complex A) a' Y₃) ≫
        eHomWhiskerRight (Complex A) a Y₃ := by rw [wg]
    _ = _ := by rw [eHomWhiskerRight_comp, Category.assoc]

end SerrePositivity.DifferentialGraded
