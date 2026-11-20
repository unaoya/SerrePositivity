module

public import SerrePositivity.Spectra.General.Basic

/-! # 対称スペクトルの各次数の構造射

convolutionの標準射にSym(K)の作用を合成して構造射を得る。
置換の同変性、スペクトルの射との両立、単位・結合の整合性を証明する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] {K : C}

/-- The canonical Day-convolution generator at a pair of degrees. -/
def pairing (F G : SymmetricSequence C) (p q : ℕ) :
    SymmetricSequence.level F p ⊗ SymmetricSequence.level G q ⟶
      SymmetricSequence.level (SymmetricSequence.convolution F G) (p + q) :=
  (SymmetricSequence.convolutionUnit F G).app (FiniteBijection.of p, FiniteBijection.of q)

omit [SymmetricCategory C] [MonoidalClosed C] in
lemma pairing_equivariance (F G : SymmetricSequence C) (p q : ℕ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    (F.map (FiniteBijection.permutation p σ) ⊗ₘ G.map (FiniteBijection.permutation q τ)) ≫
      pairing F G p q = pairing F G p q ≫ (SymmetricSequence.convolution F G).map
        (FiniteBijection.sumMap (FiniteBijection.permutation p σ)
          (FiniteBijection.permutation q τ)) := by
  have h := (SymmetricSequence.convolutionUnit F G).naturality
    (show (FiniteBijection.of p, FiniteBijection.of q) ⟶
        (FiniteBijection.of p, FiniteBijection.of q) from
      (FiniteBijection.permutation p σ, FiniteBijection.permutation q τ))
  simpa [pairing, externalProduct, externalProductBifunctor, tensorHom_def,
    FiniteBijection.sumFunctor, FiniteBijection.sumObj, SymmetricSequence.level] using h


/-- 各次数のSym(K)とスペクトルのレベルから和次数への構造射。 -/
def structureMap (E : GeneralSymmetricSpectrum C K) (p q : ℕ) :
    TensorPowers.power K p ⊗ level E q ⟶ level E (p + q) :=
  pairing (SymmetricSequence.tensorPowerSequence K) E.X p q ≫
    (action E).app (FiniteBijection.of (p + q))
/-- 各次数の構造射は左右ブロックの置換と両立する。 -/
lemma structureMap_equivariance (E : GeneralSymmetricSpectrum C K) (p q : ℕ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    ((SymmetricSequence.tensorPowerSequence K).map (FiniteBijection.permutation p σ) ⊗ₘ
        E.X.map (FiniteBijection.permutation q τ)) ≫ structureMap E p q =
      structureMap E p q ≫ E.X.map
        (FiniteBijection.sumMap (FiniteBijection.permutation p σ)
          (FiniteBijection.permutation q τ)) := by
  simp only [structureMap, Category.assoc]
  rw [← Category.assoc, pairing_equivariance,
    Category.assoc]
  erw [NatTrans.naturality (action E)]
/-- スペクトルの射の成分は各次数の構造射と両立する。 -/
lemma structureMap_hom {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F) (p q : ℕ) :
    structureMap E p q ≫ f.hom.app (FiniteBijection.of (p + q)) =
      (𝟙 (TensorPowers.power K p) ⊗ₘ f.hom.app (FiniteBijection.of q)) ≫ structureMap F p q := by
  have haction : action E ≫ f.hom =
      SymmetricSequence.tensorPowerSequence K ◁ f.hom ≫ action F :=
    IsModHom.smul_hom (A := SymmetricSequence.tensorPowerSequence K) (f := f.hom)
  have h := congrArg (fun η ↦ η.app (FiniteBijection.of (p + q))) haction
  erw [NatTrans.comp_app, NatTrans.comp_app] at h
  simp only [structureMap, Category.assoc]
  erw [h]
  have hc := SymmetricSequence.convolutionUnit_whiskerLeft
    (SymmetricSequence.tensorPowerSequence K) f.hom
    (FiniteBijection.of p) (FiniteBijection.of q)
  simp only [MonoidalCategory.id_tensorHom]
  change pairing (SymmetricSequence.tensorPowerSequence K) E.X p q ≫
      ((SymmetricSequence.tensorPowerSequence K) ◁ f.hom).app (FiniteBijection.of (p + q)) =
    (TensorPowers.power K p ◁ f.hom.app (FiniteBijection.of q)) ≫
      pairing (SymmetricSequence.tensorPowerSequence K) F.X p q at hc
  erw [← Category.assoc, hc, Category.assoc]

/-- 第0段の構造射は単位子と添字の移送による射。 -/
lemma structureMap_unit (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    structureMap E 0 n = (λ_ (level E n)).hom ≫
      E.X.map (FiniteBijection.sumLeftUnitor (FiniteBijection.of n)).inv := by
  have h := congrArg (fun η ↦
    ((SymmetricSequence.convolutionUnitCan (C := C)).app ⟨⟨⟩⟩ ▷ level E n) ≫
      (SymmetricSequence.convolutionUnit SymmetricSequence.convolutionTensorUnit E.X).app
        (FiniteBijection.of 0, FiniteBijection.of n) ≫
      η.app (FiniteBijection.of (0 + n)))
    (ModObj.one_smul_self (SymmetricSequence.tensorPowerSequence K) E.X)
  erw [NatTrans.comp_app] at h
  erw [SymmetricSequence.convolutionUnit_whiskerRight_assoc] at h
  erw [← comp_whiskerRight_assoc, SymmetricSequence.tensorPowerUnit_fac_app,
    id_whiskerRight, Category.id_comp] at h
  erw [SymmetricSequence.convolution_leftUnitor_generator] at h
  exact h

/-- Sym(K)の二段の連結と、各次数の構造射の反復との両立。 -/
lemma structureMap_assoc (E : GeneralSymmetricSpectrum C K) (p q r : ℕ) :
    ((TensorPowers.appendIso K p q).hom ▷ level E r) ≫ structureMap E (p + q) r =
      (α_ (TensorPowers.power K p) (TensorPowers.power K q) (level E r)).hom ≫
        (TensorPowers.power K p ◁ structureMap E q r) ≫ structureMap E p (q + r) ≫
        E.X.map (FiniteBijection.sumAssociator
          (FiniteBijection.of p) (FiniteBijection.of q) (FiniteBijection.of r)).inv := by
  have haction : SymmetricSequence.tensorPowerMultiplication K ▷ E.X ≫ action E =
      (α_ (SymmetricSequence.tensorPowerSequence K) (SymmetricSequence.tensorPowerSequence K)
        E.X).hom ≫ SymmetricSequence.tensorPowerSequence K ◁ action E ≫ action E :=
    ModObj.mul_smul_self (SymmetricSequence.tensorPowerSequence K) E.X
  have h := congrArg (fun η ↦
    ((SymmetricSequence.convolutionUnit (SymmetricSequence.tensorPowerSequence K)
        (SymmetricSequence.tensorPowerSequence K)).app
        (FiniteBijection.of p, FiniteBijection.of q) ▷ level E r) ≫
      (SymmetricSequence.convolutionUnit
        (SymmetricSequence.convolution (SymmetricSequence.tensorPowerSequence K)
          (SymmetricSequence.tensorPowerSequence K)) E.X).app
        (FiniteBijection.of (p + q), FiniteBijection.of r) ≫
      η.app (FiniteBijection.of ((p + q) + r))) haction
  erw [NatTrans.comp_app] at h
  erw [SymmetricSequence.convolutionUnit_whiskerRight_assoc] at h
  erw [← comp_whiskerRight_assoc, SymmetricSequence.tensorPowerMultiplication_fac_app] at h
  erw [SymmetricSequence.convolution_associator_generator_assoc
    (SymmetricSequence.tensorPowerSequence K) (SymmetricSequence.tensorPowerSequence K) E.X
    (FiniteBijection.of p) (FiniteBijection.of q) (FiniteBijection.of r)] at h
  erw [NatTrans.naturality ((SymmetricSequence.tensorPowerSequence K) ◁ action E ≫ action E)] at h
  erw [NatTrans.comp_app] at h
  simp only [Category.assoc] at h
  erw [SymmetricSequence.convolutionUnit_whiskerLeft_assoc] at h
  simpa only [structureMap, pairing,
    Category.assoc, MonoidalCategory.whiskerLeft_comp, FiniteBijection.sumObj,
    FiniteBijection.card_of, FiniteBijection.sumFunctor, level, SymmetricSequence.level,
    SymmetricSequence.tensorPowerSequence, TensorPowers.bijectionFunctor,
    FiniteBijection.familyFunctor, externalProductBifunctor_obj_obj] using h

end SerrePositivity.GeneralSymmetricSpectrum
