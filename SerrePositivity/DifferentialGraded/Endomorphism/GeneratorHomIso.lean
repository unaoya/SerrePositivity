module
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementComparison
public import SerrePositivity.DifferentialGraded.Module.HomWhisker
public import Mathlib.CategoryTheory.Enriched.HomCongr

/-! # 指定対象を始域とする再構成Hom写像とdg Yoneda -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 正則End加群とHom(E,E)の閉零同型。 -/
def endomorphismRegularModuleIso :
    ForgetEnrichment.of (Complex A) (representable A (EndomorphismObject.point (E := E))) ≅
      ForgetEnrichment.of (Complex A) ((endomorphismModuleHom A D E).obj E) :=
  (eqToIso (congrArg (ForgetEnrichment.of (Complex A)) (endomorphismModuleHom_self A D E))).symm

lemma endomorphismRegularModuleIso_hom_eval (b : EndomorphismObject E) :
    (moduleEvaluation A (EndomorphismObject E) b).map
      (endomorphismRegularModuleIso A D E).hom = 𝟙 _ := by
  change (moduleEvaluation A (EndomorphismObject E) b).map
    (eqToHom (congrArg (ForgetEnrichment.of (Complex A))
      (endomorphismModuleHom_self A D E)).symm) = _
  rw [eqToHom_map]
  rfl

lemma endomorphismGeneratorYonedaApp (M : RightModule A D) (b : EndomorphismObject E) :
    yonedaExtensionApp A (EndomorphismObject.point (E := E))
        ((endomorphismModuleHom A D E).obj M) (𝟙 _) (op b) =
      (leftRepresentable A E).map E M := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [yonedaExtensionApp_apply]
  change (p * r).negOnePow • forward A (D := RightModule A D) m f hn = _
  exact (leftRepresentable_action A E E M f m hn).symm

lemma endomorphismModuleHom_generator_map_yoneda (M : RightModule A D) :
    (endomorphismModuleHom A D E).map E M ≫
        moduleHomPrecompose A (EndomorphismObject E)
          (representable A (EndomorphismObject.point (E := E)))
          ((endomorphismModuleHom A D E).obj E) ((endomorphismModuleHom A D E).obj M)
          (endomorphismRegularModuleIso A D E).hom =
      (dgYonedaIso A (EndomorphismObject.point (E := E))
        ((endomorphismModuleHom A D E).obj M)).inv := by
  apply moduleHom_ext
  intro b
  rw [Category.assoc, moduleHomPrecompose_π]
  change (endomorphismModuleHom A D E).map E M ≫
    moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj E)
      ((endomorphismModuleHom A D E).obj M) b ≫
      homPrecompose ((moduleEvaluation A (EndomorphismObject E) b).map
        (endomorphismRegularModuleIso A D E).hom) (moduleHom A D E M) = _
  rw [endomorphismRegularModuleIso_hom_eval]
  have hid : homPrecompose (𝟙 (moduleHom A D E E)) (moduleHom A D E M) = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Cochain.id_comp z
  change (endomorphismModuleHom A D E).map E M ≫
    moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj E)
      ((endomorphismModuleHom A D E).obj M) b ≫
      homPrecompose (𝟙 (moduleHom A D E E)) (moduleHom A D E M) = _
  rw [hid]
  have hcalc : (endomorphismModuleHom A D E).map E M ≫
      moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj E)
        ((endomorphismModuleHom A D E).obj M) b =
      (dgYonedaIso A (EndomorphismObject.point (E := E))
        ((endomorphismModuleHom A D E).obj M)).inv ≫
        moduleHomπ A (EndomorphismObject E) (representable A .point)
          ((endomorphismModuleHom A D E).obj M) b := by
    cases b
    have hy := moduleHomEquiv_symm_π A (EndomorphismObject E) _
      (representable A .point) ((endomorphismModuleHom A D E).obj M)
      (yonedaExtension A .point ((endomorphismModuleHom A D E).obj M) (𝟙 _)) .point
    exact (endomorphismModuleHom_map_π A D E E M).trans
      ((endomorphismGeneratorYonedaApp A D E M .point).symm.trans hy.symm)
  exact (Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans hcalc)

/-- 始域Eからの全Hom写像はchain iso。Eの射影性・compact性は不要。 -/
lemma endomorphismModuleHom_generator_isIso (M : RightModule A D) :
    IsIso ((endomorphismModuleHom A D E).map E M) := by
  let i := endomorphismRegularModuleIso A D E
  let α := Iso.eHomCongr (Complex A) i.symm
    (Iso.refl (ForgetEnrichment.of (Complex A) ((endomorphismModuleHom A D E).obj M)))
  have hα : α.hom = moduleHomPrecompose A (EndomorphismObject E)
      (representable A (EndomorphismObject.point (E := E)))
      ((endomorphismModuleHom A D E).obj E) ((endomorphismModuleHom A D E).obj M) i.hom := by
    simp [α, Iso.eHomCongr, moduleHomPrecompose]
  have : IsIso (moduleHomPrecompose A (EndomorphismObject E)
      (representable A (EndomorphismObject.point (E := E)))
      ((endomorphismModuleHom A D E).obj E) ((endomorphismModuleHom A D E).obj M) i.hom) := by
    rw [← hα]
    infer_instance
  exact IsIso.of_isIso_fac_right (endomorphismModuleHom_generator_map_yoneda A D E M)

lemma endomorphismModuleHom_generator_quasiIso (M : RightModule A D) :
    QuasiIso ((endomorphismModuleHom A D E).map E M) := by
  have := endomorphismModuleHom_generator_isIso A D E M
  infer_instance

end SerrePositivity.DifferentialGraded
