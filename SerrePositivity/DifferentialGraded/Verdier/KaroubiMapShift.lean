module
public import SerrePositivity.DifferentialGraded.Verdier.KaroubiSquareShift

/-! # Karoubi 延長の合成比較と自然同型の shift 整合性 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents
variable {C E T : Type*} [Category* C] [Category* E] [Category* T]
  [HasShift C ℤ] [HasShift E ℤ] [HasShift T ℤ]

/-- 元の Karoubi 因子化を、合成関手を明記した型で用いる。 -/
def karoubiFactor (F : C ⥤ E) :
    toKaroubi C ⋙ (functorExtension₂ C E).obj F ≅ F ⋙ toKaroubi E :=
  (functorExtension₂CompWhiskeringLeftToKaroubiIso C E).app F

instance karoubiFactorCommShift (F : C ⥤ E) [F.CommShift ℤ] :
    NatTrans.CommShift (karoubiFactor F).hom ℤ := karoubiExtensionFactors_commShift F

variable (F : C ⥤ E) [F.CommShift ℤ] (G : E ⥤ T) [G.CommShift ℤ]

def karoubiCompositionRestrictedSquare :
    toKaroubi C ⋙ ((functorExtension₂ C E).obj F ⋙ (functorExtension₂ E T).obj G) ≅
      toKaroubi C ⋙ (functorExtension₂ C T).obj (F ⋙ G) :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (karoubiFactor F) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F (karoubiFactor G) ≪≫
    (Functor.associator _ _ _).symm ≪≫ (karoubiFactor (F ⋙ G)).symm

instance karoubiCompositionRestrictedSquareCommShift :
    NatTrans.CommShift (karoubiCompositionRestrictedSquare F G).hom ℤ := by
  dsimp only [karoubiCompositionRestrictedSquare, Iso.trans_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom]
  infer_instance

omit [HasShift C ℤ] [HasShift E ℤ] [HasShift T ℤ] [F.CommShift ℤ] [G.CommShift ℤ] in
lemma karoubiComposition_whisker :
    whiskerLeft (toKaroubi C) (karoubiFunctorCompositionIso F G).hom =
      (karoubiCompositionRestrictedSquare F G).hom := by
  apply NatTrans.ext
  funext X
  apply Karoubi.hom_ext
  simp only [comp_obj, karoubiFunctorCompositionIso, Iso.refl_hom, whiskerLeft_id', NatTrans.id_app,
    Karoubi.id_f, functorExtension₂_obj_obj_p, toKaroubi_obj_X, toKaroubi_obj_p, map_id,
    karoubiCompositionRestrictedSquare, karoubiFactor, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, Iso.app_hom, isoWhiskerLeft_hom, Iso.app_inv, NatTrans.comp_app,
    associator_inv_app, whiskerRight_app, associator_hom_app, whiskerLeft_app, Category.id_comp,
    Karoubi.comp_f, functorExtension₂_obj_map_f,
    functorExtension₂CompWhiskeringLeftToKaroubiIso_hom_app_app_f,
    functorExtension₂CompWhiskeringLeftToKaroubiIso_inv_app_app_f, Category.comp_id]
  exact (Category.comp_id _).symm

instance karoubiFunctorCompositionIsoCommShift :
    NatTrans.CommShift (karoubiFunctorCompositionIso F G).hom ℤ := by
  let := (whiskeringLeftObjToKaroubiFullyFaithful (C := C) (D := Karoubi T)).faithful
  refine natTransCommShift_of_precomp (toKaroubi C) _ (hτ := ?_)
  rw [karoubiComposition_whisker]
  infer_instance

section Map
variable {F G} {F' : C ⥤ E} [F'.CommShift ℤ] (α : F ≅ F') [NatTrans.CommShift α.hom ℤ]

def karoubiMapRestrictedSquare :
    toKaroubi C ⋙ (functorExtension₂ C E).obj F ≅
      toKaroubi C ⋙ (functorExtension₂ C E).obj F' :=
  karoubiFactor F ≪≫ isoWhiskerRight α (toKaroubi E) ≪≫ (karoubiFactor F').symm

instance karoubiMapRestrictedSquareCommShift :
    NatTrans.CommShift (karoubiMapRestrictedSquare α).hom ℤ := by
  dsimp only [karoubiMapRestrictedSquare, Iso.trans_hom, isoWhiskerRight_hom]
  infer_instance

omit [HasShift C ℤ] [HasShift E ℤ] [F.CommShift ℤ] [F'.CommShift ℤ]
    [NatTrans.CommShift α.hom ℤ] in
lemma karoubiMap_whisker :
    whiskerLeft (toKaroubi C) ((functorExtension₂ C E).mapIso α).hom =
      (karoubiMapRestrictedSquare α).hom := by
  apply NatTrans.ext
  funext X
  apply Karoubi.hom_ext
  simp only [comp_obj, mapIso_hom, whiskerLeft_app, functorExtension₂_map_app_f, toKaroubi_obj_X,
    toKaroubi_obj_p, map_id, Category.comp_id, karoubiMapRestrictedSquare, karoubiFactor,
    Iso.trans_hom, Iso.app_hom, isoWhiskerRight_hom, Iso.symm_hom, Iso.app_inv,
    NatTrans.comp_app, whiskerRight_app, Karoubi.comp_f,
    functorExtension₂CompWhiskeringLeftToKaroubiIso_hom_app_app_f, toKaroubi_map_f,
    functorExtension₂CompWhiskeringLeftToKaroubiIso_inv_app_app_f]
  exact (Category.id_comp (α.hom.app X)).symm

instance karoubiMapIsoCommShift :
    NatTrans.CommShift ((functorExtension₂ C E).mapIso α).hom ℤ := by
  let := (whiskeringLeftObjToKaroubiFullyFaithful (C := C) (D := Karoubi E)).faithful
  refine natTransCommShift_of_precomp (toKaroubi C) _ (hτ := ?_)
  rw [karoubiMap_whisker]
  infer_instance
end Map

variable {E' : Type*} [Category* E'] [HasShift E' ℤ]
  {F' : C ⥤ E'} {G' : E' ⥤ T} [F'.CommShift ℤ] [G'.CommShift ℤ]
  (e : F ⋙ G ≅ F' ⋙ G') [NatTrans.CommShift e.hom ℤ]

instance karoubiFunctorSquareCommShift : NatTrans.CommShift (karoubiFunctorSquare F G e).hom ℤ := by
  dsimp only [karoubiFunctorSquare, Iso.trans_hom]
  infer_instance
end SerrePositivity.DifferentialGraded
