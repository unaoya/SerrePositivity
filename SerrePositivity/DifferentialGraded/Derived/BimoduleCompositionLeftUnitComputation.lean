module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionLeftUnit

/-! # 左単位のK-flat因子での計算と任意解像度による表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma derivedBimoduleLeftUnitIso_base_app (hC : localHomKFlat A C) (Q : BimoduleCategory A B C) :
    (derivedBimoduleLeftUnitIso A B C hC).hom.app ((bimoduleToDerived A B C).obj Q) =
      (derivedBimoduleLeftUnitBaseIso A B C hC Q).hom := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)
    (bimoduleToDerived A B C ⋙ derivedBimoduleLeftUnitFunctor A B C hC) (bimoduleToDerived A B C)
    (derivedBimoduleLeftUnitFunctor A B C hC) (𝟭 _)
    (derivedBimoduleLeftUnitLocalizedIso A B C hC).hom Q
  change (derivedBimoduleLeftUnitIso A B C hC).hom.app
      ((bimoduleToDerived A B C).obj Q) =
    𝟙 _ ≫ (derivedBimoduleLeftUnitBaseIso A B C hC Q).hom ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

lemma derivedBimoduleLeftUnitResolutionIso_self (hC : localHomKFlat A C)
    (R : RightKFlatBimoduleCategory A B C) :
    (derivedBimoduleLeftUnitResolutionIso A B C hC R.obj R (𝟙 R.obj)
      ((BimoduleCategory.quasiIso A B C).id_mem R.obj)).hom =
    (derivedBimoduleComposeKFlatValueIso A B B C hC R (rightKFlatDiagonal A B).obj).hom ≫
      (bimoduleToDerived A B C).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom := by
  change ((derivedBimoduleComposeResolutionComputation A B B C hC R.obj R (𝟙 R.obj)
      ((BimoduleCategory.quasiIso A B C).id_mem R.obj)).hom.app
        ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj)) ≫
      ((bimoduleToDerived A B C).map _ ≫ (bimoduleToDerived A B C).map (𝟙 R.obj)) = _
  rw [derivedBimoduleComposeResolutionComputation_self, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

lemma derivedBimoduleLeftUnitIso_kFlat_base_app (hC : localHomKFlat A C)
    (R : RightKFlatBimoduleCategory A B C) :
    (derivedBimoduleLeftUnitIso A B C hC).hom.app ((bimoduleToDerived A B C).obj R.obj) =
      (derivedBimoduleComposeKFlatValueIso A B B C hC R (rightKFlatDiagonal A B).obj).hom ≫
        (bimoduleToDerived A B C).map
          (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom := by
  rw [derivedBimoduleLeftUnitIso_base_app]
  have h := derivedBimoduleLeftUnitResolutionIso_naturality A B C hC
    (rightKFlatResolutionObj A B C hC R.obj) R
    (bimoduleCanonicalSemifreeResolution A B C R.obj).π (𝟙 R.obj)
    (bimoduleCanonicalSemifreeResolution A B C R.obj).quasiIso
    ((BimoduleCategory.quasiIso A B C).id_mem R.obj) (𝟙 R.obj)
    (rightKFlatAugmentation A B C hC R) (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
      rfl)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm.trans (derivedBimoduleLeftUnitResolutionIso_self A B C hC R)

lemma derivedBimoduleLeftUnitResolutionIso_fac (hC : localHomKFlat A C)
    (Q : BimoduleCategory A B C) (R : RightKFlatBimoduleCategory A B C)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A B C q) :
    (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map q) ≫
        (derivedBimoduleLeftUnitResolutionIso A B C hC Q R q hq).hom =
      (derivedBimoduleComposeKFlatValueIso A B B C hC R (rightKFlatDiagonal A B).obj).hom ≫
        (bimoduleToDerived A B C).map
          (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom ≫
        (bimoduleToDerived A B C).map q := by
  have h := NatTrans.congr_app (derivedBimoduleComposeResolutionComputation_fac A B B C hC Q R q hq)
    ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj)
  simp only [NatTrans.comp_app] at h
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫
      ((bimoduleToDerived A B C).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom ≫
          (bimoduleToDerived A B C).map q)) h)

/-- 左単位の自然同型は、任意の指定K-flat解像度から作った表示に一致する。 -/
lemma derivedBimoduleLeftUnitIso_resolution_app (hC : localHomKFlat A C)
    (Q : BimoduleCategory A B C) (R : RightKFlatBimoduleCategory A B C)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A B C q) :
    (derivedBimoduleLeftUnitIso A B C hC).hom.app ((bimoduleToDerived A B C).obj Q) =
      (derivedBimoduleLeftUnitResolutionIso A B C hC Q R q hq).hom := by
  apply (Iso.cancel_iso_hom_left
    ((derivedBimoduleLeftUnitFunctor A B C hC).mapIso (bimoduleDerivedIso A B C q hq)) _ _).1
  change (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map q) ≫ _ =
    (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map q) ≫ _
  rw [derivedBimoduleLeftUnitResolutionIso_fac]
  rw [(derivedBimoduleLeftUnitIso A B C hC).hom.naturality,
    derivedBimoduleLeftUnitIso_kFlat_base_app, Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
