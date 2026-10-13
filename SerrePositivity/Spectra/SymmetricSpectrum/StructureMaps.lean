module

public import SerrePositivity.Spectra.SymmetricSpectrum.Basic

/-! # 対称スペクトルの各次数の構造射

convolutionの標準射に球面の作用を合成して構造射を得る。
置換の同変性、スペクトルの射との両立、単位・結合の整合性を証明する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SymmetricSpectrum

open SerrePositivity.PointedSimplicialSet

/-- 各次数の球面とスペクトルのレベルから和次数への構造射。 -/
def structureMap (E : SymmetricSpectrum.{u}) (p q : ℕ) :
    PointedObject.smash (spherePower.{u} p) (level E q) ⟶ level E (p + q) :=
  PointedSymmetricSequence.convolutionPairing sphereSequence.{u} E.X p q ≫
    (action E).app (FiniteBijection.of (p + q))
/-- 各次数の構造射は左右ブロックの置換と両立する。 -/
lemma structureMap_equivariance (E : SymmetricSpectrum.{u}) (p q : ℕ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    PointedObject.smashMap (spherePermutationAction.{u} p σ).asIso.hom
        (E.X.map (FiniteBijection.permutation q τ)) ≫ structureMap E p q =
      structureMap E p q ≫ E.X.map
        (FiniteBijection.sumMap (FiniteBijection.permutation p σ)
          (FiniteBijection.permutation q τ)) := by
  rw [← sphereSequence_map_permutation]
  simp only [structureMap, Category.assoc]
  rw [← Category.assoc, PointedSymmetricSequence.convolutionPairing_equivariance,
    Category.assoc]
  erw [NatTrans.naturality (action E)]
/-- スペクトルの射の成分は各次数の構造射と両立する。 -/
lemma structureMap_hom {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) (p q : ℕ) :
    structureMap E p q ≫ f.hom.app (FiniteBijection.of (p + q)) =
      PointedObject.smashMap (𝟙 (spherePower.{u} p))
          (f.hom.app (FiniteBijection.of q)) ≫ structureMap F p q := by
  have h := congrArg (fun η ↦ η.app (FiniteBijection.of (p + q))) (action_hom f)
  erw [NatTrans.comp_app, NatTrans.comp_app] at h
  simp only [structureMap, Category.assoc]
  erw [h]
  have hc := SymmetricSequence.convolutionUnit_whiskerLeft sphereSequence.{u} f.hom
    (FiniteBijection.of p) (FiniteBijection.of q)
  change PointedSymmetricSequence.convolutionPairing sphereSequence.{u} E.X p q ≫
      (sphereSequence.{u} ◁ f.hom).app (FiniteBijection.of (p + q)) =
    PointedObject.smashMap (𝟙 (spherePower.{u} p)) (f.hom.app (FiniteBijection.of q)) ≫
      PointedSymmetricSequence.convolutionPairing sphereSequence.{u} F.X p q at hc
  erw [← Category.assoc, hc, Category.assoc]

/-- 第0段の構造射は単位子と添字の移送による射。 -/
lemma structureMap_unit (E : SymmetricSpectrum.{u}) (n : ℕ) :
    structureMap E 0 n = (λ_ (level E n)).hom ≫
      E.X.map (FiniteBijection.sumLeftUnitor (FiniteBijection.of n)).inv := by
  have h := congrArg (fun η ↦
    ((SymmetricSequence.convolutionUnitCan (C := PointedSimplicialSet.{u})).app ⟨⟨⟩⟩ ▷ level E n) ≫
      (SymmetricSequence.convolutionUnit SymmetricSequence.convolutionTensorUnit E.X).app
        (FiniteBijection.of 0, FiniteBijection.of n) ≫
      η.app (FiniteBijection.of (0 + n))) (action_unit E)
  erw [NatTrans.comp_app] at h
  erw [SymmetricSequence.convolutionUnit_whiskerRight_assoc] at h
  erw [← comp_whiskerRight_assoc, sphereUnit_fac_app, id_whiskerRight, Category.id_comp] at h
  erw [SymmetricSequence.convolution_leftUnitor_generator] at h
  exact h

/-- 球面の二段の連結と、各次数の構造射の反復との両立。 -/
lemma structureMap_assoc (E : SymmetricSpectrum.{u}) (p q r : ℕ) :
    ((spherePowerAppendIso.{u} p q).hom ▷ level E r) ≫ structureMap E (p + q) r =
      (α_ (spherePower.{u} p) (spherePower.{u} q) (level E r)).hom ≫
        (spherePower.{u} p ◁ structureMap E q r) ≫ structureMap E p (q + r) ≫
        E.X.map (FiniteBijection.sumAssociator
          (FiniteBijection.of p) (FiniteBijection.of q) (FiniteBijection.of r)).inv := by
  have h := congrArg (fun η ↦
    ((SymmetricSequence.convolutionUnit sphereSequence.{u} sphereSequence.{u}).app
        (FiniteBijection.of p, FiniteBijection.of q) ▷ level E r) ≫
      (SymmetricSequence.convolutionUnit
        (SymmetricSequence.convolution sphereSequence.{u} sphereSequence.{u}) E.X).app
        (FiniteBijection.of (p + q), FiniteBijection.of r) ≫
      η.app (FiniteBijection.of ((p + q) + r))) (action_assoc E)
  erw [NatTrans.comp_app] at h
  erw [SymmetricSequence.convolutionUnit_whiskerRight_assoc] at h
  erw [← comp_whiskerRight_assoc, sphereMultiplication_fac_app] at h
  erw [SymmetricSequence.convolution_associator_generator_assoc
    sphereSequence.{u} sphereSequence.{u} E.X
    (FiniteBijection.of p) (FiniteBijection.of q) (FiniteBijection.of r)] at h
  erw [NatTrans.naturality (sphereSequence.{u} ◁ action E ≫ action E)] at h
  erw [NatTrans.comp_app] at h
  simp only [Category.assoc] at h
  erw [SymmetricSequence.convolutionUnit_whiskerLeft_assoc] at h
  simpa only [structureMap, PointedSymmetricSequence.convolutionPairing,
    Category.assoc, MonoidalCategory.whiskerLeft_comp, FiniteBijection.sumObj,
    FiniteBijection.card_of, FiniteBijection.sumFunctor, level, SymmetricSequence.level,
    sphereSequence, SymmetricSequence.tensorPowerSequence, TensorPowers.bijectionFunctor,
    FiniteBijection.familyFunctor, spherePower, externalProductBifunctor_obj_obj] using h

end SerrePositivity.SymmetricSpectrum
