module
public import SerrePositivity.DifferentialGraded.Module.HomWhisker

/-! # 可逆な加群射による全Hom可換四角形の逆向き -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

lemma moduleHom_iso_square_inv {K : Complex A} {X Y X' Y' : ModuleCategory A B}
    (f : K ⟶ (X ⟶[Complex A] Y)) (g : K ⟶ (X' ⟶[Complex A] Y'))
    (a : X ≅ X') (b : Y ≅ Y')
    (h : f ≫ eHomWhiskerLeft (Complex A) X b.hom =
      g ≫ eHomWhiskerRight (Complex A) a.hom Y') :
    g ≫ eHomWhiskerLeft (Complex A) X' b.inv =
      f ≫ eHomWhiskerRight (Complex A) a.inv Y := by
  have hh := congrArg (fun k : K ⟶ (X ⟶[Complex A] Y') =>
    k ≫ eHomWhiskerLeft (Complex A) X b.inv ≫
      eHomWhiskerRight (Complex A) a.inv Y) h
  simp only [Category.assoc, ← eHomWhiskerLeft_comp_assoc, Iso.hom_inv_id,
    eHomWhiskerLeft_id, Category.id_comp] at hh
  rw [← eHom_whisker_exchange_assoc] at hh
  simp only [← eHomWhiskerRight_comp, Iso.inv_hom_id, eHomWhiskerRight_id,
    Category.comp_id] at hh
  exact hh.symm

lemma moduleIso_closed_hom_inv {X Y : ModuleCategory A B} (a : X ≅ Y) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      (eHomEquiv (Complex A) a.hom ⊗ₘ eHomEquiv (Complex A) a.inv) ≫
        eComp (Complex A) X Y X = eId (Complex A) X := by
  rw [← eHomEquiv_comp, Iso.hom_inv_id, eHomEquiv_id]

end SerrePositivity.DifferentialGraded
