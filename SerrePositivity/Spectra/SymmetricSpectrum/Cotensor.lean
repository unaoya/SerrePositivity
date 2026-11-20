module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHomFree
public import SerrePositivity.Spectra.SymmetricSequence.UnshiftedInternalHom
public import SerrePositivity.Spectra.General.ShiftedHomZero
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.Free
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation
public import SerrePositivity.Spectra.SymmetricSpectrum.Suspension

/-! # 各段の通常の内部Homを持つ対称スペクトル

生成次数零の比較で球面作用を移し、F_0からの内部Homとスペクトル全体で比較する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level structureMap structureMap_hom
  internalHom internalHomFreeZeroLevelIso internalHomShiftIso shiftedHom
  unshiftedHomLevelIso unshiftedHomLevelIso_structureMap
  unshiftedHomLevelIso_suspensionMap unshiftedHomStructureFormula unshiftedHomSuspensionFormula)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet
open MonoidalModuleInternalHom (freeHomModuleIso)

/-- 自由対称列からの内部Homを各段の通常の内部Homへ比較する。 -/
abbrev homBySequenceCotensorIso (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :=
  SymmetricSequence.freeInternalHomSequenceIso 0 X E.X ≪≫ SymmetricSequence.zeroShiftInternalHomIso X E.X

/-- 各段がXから値域の同じ段への通常の内部Homであるスペクトル。 -/
def cotensor (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} :=
  MonoidalModuleInternalHom.transportedObj (C := PointedSymmetricSequence.{u})
    sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E (homBySequenceCotensorIso X E)

/-- cotensorの第q段は通常の内部Homと定義的に一致する。 -/
lemma cotensor_level (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) (q : ℕ) :
    level (cotensor X E) q = (ihom X).obj (level E q) := by
  rfl

/-- cotensorの置換作用は値域の同じ段の置換による後合成。 -/
lemma cotensor_permutation (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u})
    (q : ℕ) (σ : Equiv.Perm (Fin q)) :
    (cotensor X E).X.map (FiniteBijection.permutation q σ) =
      (ihom X).map (E.X.map (FiniteBijection.permutation q σ)) := by
  rfl

/-- 生成次数零のずれを除くスペクトル全体の比較。 -/
def shiftedHomCotensorIso (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    shiftedHom 0 X E ≅ cotensor X E :=
  MonoidalModuleInternalHom.furtherTransportedIso (C := PointedSymmetricSequence.{u})
    sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E
      (SymmetricSequence.freeInternalHomSequenceIso 0 X E.X) (SymmetricSequence.zeroShiftInternalHomIso X E.X)

/-- ずれを除くスペクトル比較の基礎射は対称列の比較の順射。 -/
lemma shiftedHomCotensorIso_hom (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    (shiftedHomCotensorIso X E).hom.hom =
      (SymmetricSequence.zeroShiftInternalHomIso X E.X).hom :=
  MonoidalModuleInternalHom.furtherTransportedIso_hom
    (C := PointedSymmetricSequence.{u}) sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E
      (SymmetricSequence.freeInternalHomSequenceIso 0 X E.X) (SymmetricSequence.zeroShiftInternalHomIso X E.X)

/-- ずれを除くスペクトル比較の基礎逆射は対称列の比較の逆射。 -/
lemma shiftedHomCotensorIso_inv (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    (shiftedHomCotensorIso X E).inv.hom =
      (SymmetricSequence.zeroShiftInternalHomIso X E.X).inv :=
  MonoidalModuleInternalHom.furtherTransportedIso_inv
    (C := PointedSymmetricSequence.{u}) sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E
      (SymmetricSequence.freeInternalHomSequenceIso 0 X E.X) (SymmetricSequence.zeroShiftInternalHomIso X E.X)

/-- スペクトル比較の第q成分は前段階の各段の比較。 -/
lemma shiftedHomCotensorIso_hom_app (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (shiftedHomCotensorIso X E).hom.hom.app (FiniteBijection.of q) =
      (unshiftedHomLevelIso q X E).hom := by
  rw [shiftedHomCotensorIso_hom, SymmetricSequence.zeroShiftInternalHomIso_hom_app]
  exact eqToHom_map (ihom X) (congrArg (level E) (Nat.zero_add q))

/-- スペクトル逆比較の第q成分も前段階の各段の逆比較。 -/
lemma shiftedHomCotensorIso_inv_app (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (shiftedHomCotensorIso X E).inv.hom.app (FiniteBijection.of q) =
      (unshiftedHomLevelIso q X E).inv := by
  rw [shiftedHomCotensorIso_inv, SymmetricSequence.zeroShiftInternalHomIso_inv_app]
  change (ihom X).map (eqToHom (congrArg (level E) (Nat.zero_add q).symm)) =
    eqToHom (congrArg (fun k => (ihom X).obj (level E k)) (Nat.zero_add q).symm)
  erw [eqToHom_map]

/-- F_0からの内部Homとcotensorのスペクトル全体の比較。 -/
def internalHomCotensorIso (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    internalHom ((freeAt 0).obj X) E ≅ cotensor X E :=
  freeHomModuleIso sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E ≪≫
    MonoidalModuleInternalHom.transportedIso (C := PointedSymmetricSequence.{u})
      sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E (homBySequenceCotensorIso X E)

/-- F_0からの全体の比較の第q成分は前段階の各段の比較。 -/
lemma internalHomCotensorIso_hom_app (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (internalHomCotensorIso X E).hom.hom.app (FiniteBijection.of q) =
      (internalHomFreeZeroLevelIso q X E).hom := by
  have hcomp :
      internalHomCotensorIso X E = internalHomShiftIso 0 X E ≪≫ shiftedHomCotensorIso X E := by
    as_aux_lemma =>
      let freeComparison := freeHomModuleIso sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E
      let shifted := MonoidalModuleInternalHom.transportedIso sphereSequence.{u}
        ((SymmetricSequence.freeAt 0).obj X) E (SymmetricSequence.freeInternalHomSequenceIso 0 X E.X)
      let unshifted := MonoidalModuleInternalHom.transportedIso sphereSequence.{u}
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
lemma internalHomCotensorIso_inv_app (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (internalHomCotensorIso X E).inv.hom.app (FiniteBijection.of q) =
      (internalHomFreeZeroLevelIso q X E).inv := by
  change (SymmetricSequence.zeroShiftInternalHomIso X E.X).inv.app (FiniteBijection.of q) ≫
      (internalHomShiftIso 0 X E).inv.hom.app (FiniteBijection.of q) = _
  rw [← shiftedHomCotensorIso_inv]
  rw [shiftedHomCotensorIso_inv_app]
  rfl

/-- cotensorの構造射は、値域の構造射と通常の評価による直接公式。 -/
lemma cotensor_structureMap (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u})
    (p q : ℕ) :
    structureMap (cotensor X E) p q = unshiftedHomStructureFormula p q X E := by
  have h := structureMap_hom (shiftedHomCotensorIso X E).hom p q
  rw [shiftedHomCotensorIso_hom_app, shiftedHomCotensorIso_hom_app,
    unshiftedHomLevelIso_structureMap] at h
  simp only [id_tensorHom] at h
  apply (cancel_epi (spherePower.{u} p ◁ (unshiftedHomLevelIso q X E).hom)).mp
  exact h.symm

/-- cotensorの懸垂射も、値域の懸垂射と通常の評価による直接公式。 -/
lemma cotensor_suspensionMap (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u})
    (q : ℕ) :
    suspensionMap (cotensor X E) q = unshiftedHomSuspensionFormula q X E := by
  have h := GeneralSymmetricSpectrum.suspensionMap_hom (shiftedHomCotensorIso X E).hom q
  simp only [GeneralSymmetricSpectrum.levelMap] at h
  rw [shiftedHomCotensorIso_hom_app, shiftedHomCotensorIso_hom_app,
    unshiftedHomLevelIso_suspensionMap] at h
  apply (cancel_epi ((circle : PointedSimplicialSet.{u}) ◁ (unshiftedHomLevelIso q X E).hom)).mp
  exact h.symm

end SerrePositivity.SymmetricSpectrum
