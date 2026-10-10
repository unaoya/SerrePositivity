module

public import SerrePositivity.CategoryTheory.KaroubiPretriangulated
public import SerrePositivity.CategoryTheory.CommShiftOfPrecomp

/-! # 三角関手の Karoubi 包絡への延長 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
open CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]

noncomputable instance karoubiExtension_commShift :
    ((functorExtension₂ C D).obj F).CommShift ℤ :=
  commShiftOfPrecomp (toKaroubi C) ((functorExtension₂ C D).obj F) (F ⋙ toKaroubi D)
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F)

instance karoubiExtensionFactors_commShift :
    NatTrans.CommShift (show toKaroubi C ⋙ (functorExtension₂ C D).obj F ⟶ F ⋙ toKaroubi D
      from ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F).hom) ℤ :=
  commShiftOfPrecomp_compatibility (toKaroubi C) ((functorExtension₂ C D).obj F)
    (F ⋙ toKaroubi D) ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F)

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [F.IsTriangulated]

/-- 完全三角形の retract を用いた標準構造に関して延長関手は三角関手。 -/
instance karoubiExtension_isTriangulated : ((functorExtension₂ C D).obj F).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨U, hU, ⟨r⟩⟩ := hT
    let G := (functorExtension₂ C D).obj F
    let eF : toKaroubi C ⋙ G ≅ F ⋙ toKaroubi D :=
      (functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F
    have : NatTrans.CommShift eF.hom ℤ := karoubiExtensionFactors_commShift F
    let e := ((toKaroubi C).mapTriangleCompIso G).symm.app U ≪≫
      (Functor.mapTriangleIso eF).app U ≪≫
      (F.mapTriangleCompIso (toKaroubi D)).app U
    exact karoubiDistinguished_retract
      (karoubiDistinguished_iso (karoubiDistinguished_image _ (F.map_distinguished U hU)) e)
      (r.map G.mapTriangle)

end SerrePositivity
