module
public import SerrePositivity.DifferentialGraded.Verdier.KaroubiFunctorSquare
public import SerrePositivity.DifferentialGraded.Verdier.ShiftReflection

/-! # Karoubi–Perf 自然性正方形の比較同型の shift 整合性 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance triaKaroubiPerfectFactorsCommShift :
    NatTrans.CommShift (triaKaroubiPerfectFactors A D).hom ℤ := by
  have he : whiskerRight (triaKaroubiPerfectFactors A D).hom (modulePerfectOver A D Set.univ).ι =
      (finiteCellKaroubiRealization_fac A D Set.univ).hom :=
    ((whiskeringRight _ _ _).obj (modulePerfectOver A D Set.univ).ι).map_preimage _
  let β : (toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ) ⋙
        (modulePerfectOver A D Set.univ).ι ≅
      triaToPerfect A D ⋙ (modulePerfectOver A D Set.univ).ι :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (finiteCellKaroubiToPerfectCompInclusion A D Set.univ) ≪≫
      finiteCellKaroubiRealization_fac A D Set.univ ≪≫
      ((modulePerfectOver A D Set.univ).liftCompιIso (triaInclusion A D) _).symm
  have hβ : NatTrans.CommShift β.hom ℤ := by dsimp [β]; infer_instance
  have he' : whiskerRight (triaKaroubiPerfectFactors A D).hom
      (modulePerfectOver A D Set.univ).ι = β.hom := by
    rw [he]
    apply NatTrans.ext
    funext X
    dsimp only [β, Iso.trans_hom, NatTrans.comp_app, associator_hom_app,
      isoWhiskerLeft_hom, whiskerLeft_app, finiteCellKaroubiToPerfectCompInclusion,
      ObjectProperty.liftCompιIso]
    simp only [Iso.symm_hom, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
    let a := (finiteCellKaroubiRealization_fac A D Set.univ).hom.app X
    exact (show a = 𝟙 _ ≫ 𝟙 _ ≫ a ≫ 𝟙 _ from by
      simp only [Category.id_comp, Category.comp_id])
  exact NatTrans.CommShift.of_comp_faithful
    (F₁ := toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ)
    (F₂ := triaToPerfect A D) (τ := (triaKaroubiPerfectFactors A D).hom)
    (G := (modulePerfectOver A D Set.univ).ι) (h := by rw [he']; exact hβ)

variable {A' : Type u} [CommRing A'] (E : Type w) [DGCategory A' E] [Small.{u} E]
  (G : TriaCategory A D ⥤ TriaCategory A' E) [G.CommShift ℤ]
  (T : PerfectModuleCategory A D ⥤ PerfectModuleCategory A' E) [T.CommShift ℤ]
  (e : G ⋙ triaToPerfect A' E ≅ triaToPerfect A D ⋙ T) [NatTrans.CommShift e.hom ℤ]

def triaKaroubiPerfectRestrictedSquare :
    toKaroubi (TriaCategory A D) ⋙
        ((functorExtension₂ _ _).obj G ⋙ finiteCellKaroubiToPerfect A' E Set.univ) ≅
      toKaroubi (TriaCategory A D) ⋙ (finiteCellKaroubiToPerfect A D Set.univ ⋙ T) :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (G := toKaroubi (TriaCategory A D) ⋙ (functorExtension₂ _ _).obj G)
      (H := G ⋙ toKaroubi (TriaCategory A' E))
      ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft G (triaKaroubiPerfectFactors A' E) ≪≫ e ≪≫
    isoWhiskerRight (triaKaroubiPerfectFactors A D).symm T ≪≫ Functor.associator _ _ _

instance triaKaroubiPerfectRestrictedSquareCommShift :
    NatTrans.CommShift (triaKaroubiPerfectRestrictedSquare A D E G T e).hom ℤ := by
  let : NatTrans.CommShift
      (show toKaroubi (TriaCategory A D) ⋙ (functorExtension₂ _ _).obj G ⟶
        G ⋙ toKaroubi (TriaCategory A' E) from
        ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G).hom) ℤ :=
    karoubiExtensionFactors_commShift G
  let : NatTrans.CommShift
      (show toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ ⟶
        triaToPerfect A D from (triaKaroubiPerfectFactors A D).hom) ℤ :=
    triaKaroubiPerfectFactorsCommShift A D
  let : NatTrans.CommShift
      (show toKaroubi (TriaCategory A' E) ⋙ finiteCellKaroubiToPerfect A' E Set.univ ⟶
        triaToPerfect A' E from (triaKaroubiPerfectFactors A' E).hom) ℤ :=
    triaKaroubiPerfectFactorsCommShift A' E
  dsimp only [triaKaroubiPerfectRestrictedSquare, Iso.trans_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom]
  infer_instance

instance triaKaroubiPerfectSquareCommShift :
    NatTrans.CommShift (triaKaroubiPerfectSquare A D E G T e).hom ℤ := by
  let ff := whiskeringLeftObjToKaroubiFullyFaithful
    (C := TriaCategory A D) (D := PerfectModuleCategory A' E)
  let := ff.faithful
  refine natTransCommShift_of_precomp (toKaroubi (TriaCategory A D)) _ (hτ := ?_)
  have he : whiskerLeft (toKaroubi (TriaCategory A D))
      (triaKaroubiPerfectSquare A D E G T e).hom =
      (triaKaroubiPerfectRestrictedSquare A D E G T e).hom := ff.map_preimage _
  rw [he]
  infer_instance
end SerrePositivity.DifferentialGraded
