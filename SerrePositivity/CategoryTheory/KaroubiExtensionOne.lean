module

public import SerrePositivity.CategoryTheory.KaroubiTriangulatedFunctor
public import SerrePositivity.CategoryTheory.KaroubiTriangulated

/-! # Karoubi 値の三角関手の延長 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
open CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ Karoubi D) [F.CommShift ℤ]

noncomputable instance karoubiExtensionOne_commShift :
    ((functorExtension₁ C D).obj F).CommShift ℤ :=
  commShiftOfPrecomp (toKaroubi C) ((functorExtension₁ C D).obj F) F
    ((functorExtension₁CompWhiskeringLeftToKaroubiIso C D).app F)

instance karoubiExtensionOneFactors_commShift :
    NatTrans.CommShift (show toKaroubi C ⋙ (functorExtension₁ C D).obj F ⟶ F from
      ((functorExtension₁CompWhiskeringLeftToKaroubiIso C D).app F).hom) ℤ :=
  commShiftOfPrecomp_compatibility (toKaroubi C) ((functorExtension₁ C D).obj F) F
    ((functorExtension₁CompWhiskeringLeftToKaroubiIso C D).app F)

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [F.IsTriangulated]

instance karoubiExtensionOne_isTriangulated : ((functorExtension₁ C D).obj F).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨U, hU, ⟨r⟩⟩ := hT
    let G := (functorExtension₁ C D).obj F
    let eF : toKaroubi C ⋙ G ≅ F :=
      (functorExtension₁CompWhiskeringLeftToKaroubiIso C D).app F
    have : NatTrans.CommShift eF.hom ℤ := karoubiExtensionOneFactors_commShift F
    let e := ((toKaroubi C).mapTriangleCompIso G).symm.app U ≪≫
      (Functor.mapTriangleIso eF).app U
    exact karoubiDistinguished_retract
      (karoubiDistinguished_iso (F.map_distinguished U hU) e) (r.map G.mapTriangle)

end SerrePositivity
