module

public import SerrePositivity.Spectra.General.ShiftedHomZero
public import SerrePositivity.Spectra.General.Cotensor

/-! # Level comparisons and structure maps for cotensors -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

open MonoidalModuleInternalHom (freeHomModuleIso freeHomIso)

/-- 生成次数零のずれを除くスペクトル全体の比較。 -/
def shiftedHomCotensorIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    shiftedHom 0 X E ≅ cotensor X E :=
  MonoidalModuleInternalHom.furtherTransportedIso
    (SymmetricSequence.tensorPowerSequence K) ((SymmetricSequence.freeAt 0).obj X) E
      (SymmetricSequence.freeInternalHomSequenceIso 0 X E.X)
    (SymmetricSequence.zeroShiftInternalHomIso X E.X)

/-- スペクトル比較の第q成分は前段階の各段の比較。 -/
lemma shiftedHomCotensorIso_hom_app (X : C)
    (E : GeneralSymmetricSpectrum C K) (q : ℕ) :
    (shiftedHomCotensorIso X E).hom.hom.app (FiniteBijection.of q) =
      (unshiftedHomLevelIso q X E).hom := by
  change (MonoidalModuleInternalHom.furtherTransportedIso
    (SymmetricSequence.tensorPowerSequence K) ((SymmetricSequence.freeAt 0).obj X) E
    (SymmetricSequence.freeInternalHomSequenceIso 0 X E.X)
    (SymmetricSequence.zeroShiftInternalHomIso X E.X)).hom.hom.app (FiniteBijection.of q) = _
  rw [MonoidalModuleInternalHom.furtherTransportedIso_hom,
    SymmetricSequence.zeroShiftInternalHomIso_hom_app]
  exact eqToHom_map (ihom X) (congrArg (level E) (Nat.zero_add q))

/-- スペクトル逆比較の第q成分も前段階の各段の逆比較。 -/
lemma shiftedHomCotensorIso_inv_app (X : C)
    (E : GeneralSymmetricSpectrum C K) (q : ℕ) :
    (shiftedHomCotensorIso X E).inv.hom.app (FiniteBijection.of q) =
      (unshiftedHomLevelIso q X E).inv := by
  change (MonoidalModuleInternalHom.furtherTransportedIso
    (SymmetricSequence.tensorPowerSequence K) ((SymmetricSequence.freeAt 0).obj X) E
    (SymmetricSequence.freeInternalHomSequenceIso 0 X E.X)
    (SymmetricSequence.zeroShiftInternalHomIso X E.X)).inv.hom.app (FiniteBijection.of q) = _
  rw [MonoidalModuleInternalHom.furtherTransportedIso_inv,
    SymmetricSequence.zeroShiftInternalHomIso_inv_app]
  change (ihom X).map (eqToHom (congrArg (level E) (Nat.zero_add q).symm)) =
    eqToHom (congrArg (fun k => (ihom X).obj (level E k)) (Nat.zero_add q).symm)
  erw [eqToHom_map]

/-- F_0からの全体の比較の第q成分は前段階の各段の比較。 -/
lemma internalHomCotensorIso_hom_app (X : C)
    (E : GeneralSymmetricSpectrum C K) (q : ℕ) :
    (internalHomCotensorIso X E).hom.hom.app (FiniteBijection.of q) =
      (internalHomFreeZeroLevelIso q X E).hom := by
  have hcomp :
      internalHomCotensorIso X E = internalHomShiftIso 0 X E ≪≫ shiftedHomCotensorIso X E := by
    as_aux_lemma =>
      let freeComparison := freeHomModuleIso (SymmetricSequence.tensorPowerSequence K)
        ((SymmetricSequence.freeAt 0).obj X) E
      let shifted := MonoidalModuleInternalHom.transportedIso
        (SymmetricSequence.tensorPowerSequence K)
        ((SymmetricSequence.freeAt 0).obj X) E
        (SymmetricSequence.freeInternalHomSequenceIso 0 X E.X)
      let unshifted := MonoidalModuleInternalHom.transportedIso
        (SymmetricSequence.tensorPowerSequence K)
        ((SymmetricSequence.freeAt 0).obj X) E (homBySequenceCotensorIso X E)
      change freeComparison ≪≫ unshifted =
        (freeComparison ≪≫ shifted) ≪≫ shifted.symm ≪≫ unshifted
      rw [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [hcomp]
  change (internalHomShiftIso 0 X E).hom.hom.app (FiniteBijection.of q) ≫
      (shiftedHomCotensorIso X E).hom.hom.app (FiniteBijection.of q) = _
  rw [shiftedHomCotensorIso_hom_app]
  rfl

/-- F_0からの全体の逆比較の第q成分も既存の各段の逆比較。 -/
lemma internalHomCotensorIso_inv_app (X : C)
    (E : GeneralSymmetricSpectrum C K) (q : ℕ) :
    (internalHomCotensorIso X E).inv.hom.app (FiniteBijection.of q) =
      (internalHomFreeZeroLevelIso q X E).inv := by
  have h : (evaluation q).mapIso (internalHomCotensorIso X E) =
      internalHomFreeZeroLevelIso q X E :=
    Iso.ext (internalHomCotensorIso_hom_app X E q)
  exact congrArg Iso.inv h

/-- cotensorの構造射は、値域の構造射と通常の評価による直接公式。 -/
lemma cotensor_structureMap (X : C) (E : GeneralSymmetricSpectrum C K)
    (p q : ℕ) :
    structureMap (cotensor X E) p q = unshiftedHomStructureFormula p q X E := by
  have h := structureMap_hom (shiftedHomCotensorIso X E).hom p q
  rw [shiftedHomCotensorIso_hom_app, shiftedHomCotensorIso_hom_app,
    unshiftedHomLevelIso_structureMap] at h
  simp only [id_tensorHom] at h
  apply (cancel_epi ((TensorPowers.power K p) ◁ (unshiftedHomLevelIso q X E).hom)).mp
  exact h.symm

/-- cotensorの懸垂射も、値域の懸垂射と通常の評価による直接公式。 -/
lemma cotensor_suspensionMap (X : C) (E : GeneralSymmetricSpectrum C K)
    (q : ℕ) :
    suspensionMap (cotensor X E) q = unshiftedHomSuspensionFormula q X E := by
  have h := suspensionMap_hom (shiftedHomCotensorIso X E).hom q
  simp only [levelMap] at h
  rw [shiftedHomCotensorIso_hom_app, shiftedHomCotensorIso_hom_app,
    unshiftedHomLevelIso_suspensionMap] at h
  apply (cancel_epi (K ◁ (unshiftedHomLevelIso q X E).hom)).mp
  exact h.symm

/-- cotensorの逆比較を自由原変数の比較へ戻すと、移送の逆射になる。 -/
lemma internalHomCotensorIso_inv_freeHom (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    (internalHomCotensorIso X E).inv.hom ≫
        (freeHomIso (SymmetricSequence.tensorPowerSequence K)
          ((SymmetricSequence.freeAt 0).obj X) E).hom =
      (homBySequenceCotensorIso X E).inv := by
  have hinv :
      (freeHomModuleIso (SymmetricSequence.tensorPowerSequence K)
        ((SymmetricSequence.freeAt 0).obj X) E).inv.hom =
        (freeHomIso (SymmetricSequence.tensorPowerSequence K)
        ((SymmetricSequence.freeAt 0).obj X) E).inv := by
    as_aux_lemma =>
      rfl
  have h : (internalHomCotensorIso X E).inv.hom =
      (homBySequenceCotensorIso X E).inv ≫
        (freeHomModuleIso (SymmetricSequence.tensorPowerSequence K)
          ((SymmetricSequence.freeAt 0).obj X) E).inv.hom := rfl
  rw [h, hinv]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.GeneralSymmetricSpectrum
