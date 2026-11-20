module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHomFree
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomSequenceIso
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomFreePermutation
public import SerrePositivity.Spectra.SymmetricSpectrum.Suspension

/-! # 次数をずらした内部Homスペクトル

各段の比較を対称列全体でまとめ、球面作用を移送してスペクトルとして比較する。
構造射を値域Eの構造射から直接記述する公式はInternalHomShiftStructureで証明する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level structureMap structureMap_hom)

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open SerrePositivity.PointedSimplicialSet

/-- 各段をずらした対称列への比較。 -/
abbrev homBySequenceShiftIso (n : ℕ) (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :=
  SymmetricSequence.freeInternalHomSequenceIso n X E.X

/-- 次数をずらした内部Homの対称列への球面作用の移送。 -/
@[instance_reducible] def shiftedHomAction (n : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    ModObj sphereSequence.{u} (SymmetricSequence.shiftedInternalHom n X E.X) :=
  MonoidalModuleInternalHom.transportedAction (C := PointedSymmetricSequence.{u})
    sphereSequence.{u} ((SymmetricSequence.freeAt n).obj X) E (homBySequenceShiftIso n X E)

/-- 次数をずらした内部Homを球面加群として束ねる。 -/
def shiftedHom (n : ℕ) (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} :=
  MonoidalModuleInternalHom.transportedObj (C := PointedSymmetricSequence.{u})
    sphereSequence.{u} ((SymmetricSequence.freeAt n).obj X) E (homBySequenceShiftIso n X E)

/-- 次数をずらした内部Homスペクトルの第m段。 -/
lemma shiftedHom_level (n m : ℕ) (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    level (shiftedHom n X E) m = (ihom X).obj (level E (n + m)) := rfl

/-- 作用の移送によるスペクトルとしての比較。 -/
def homBySequenceShiftSpectrumIso (n : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    homBySequence ((SymmetricSequence.freeAt n).obj X) E ≅ shiftedHom n X E :=
  MonoidalModuleInternalHom.transportedIso (C := PointedSymmetricSequence.{u})
    sphereSequence.{u} ((SymmetricSequence.freeAt n).obj X) E (homBySequenceShiftIso n X E)

/-- F_nからの内部Homと次数をずらした内部Homのスペクトルとしての同型。 -/
def internalHomShiftIso (n : ℕ) (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    internalHom ((freeAt n).obj X) E ≅ shiftedHom n X E :=
  internalHomFreeAtIso n X E ≪≫ homBySequenceShiftSpectrumIso n X E

/-- スペクトル比較の第m成分は既存の各段の比較。 -/
lemma internalHomShiftIso_hom_app (n m : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomShiftIso n X E).hom.hom.app (FiniteBijection.of m) =
      (internalHomFreeAtLevelIso n m X E).hom := rfl

/-- スペクトルの逆比較の第m成分は既存の各段の逆比較。 -/
lemma internalHomShiftIso_inv_app (n m : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomShiftIso n X E).inv.hom.app (FiniteBijection.of m) =
      (internalHomFreeAtLevelIso n m X E).inv := rfl

/-- 各段の比較は全ての球面次数の構造射と両立する。 -/
lemma internalHomFreeAtLevelIso_structureMap (n p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    structureMap (internalHom ((freeAt n).obj X) E) p q ≫
        (internalHomFreeAtLevelIso n (p + q) X E).hom =
      PointedObject.smashMap (𝟙 (spherePower.{u} p))
        (internalHomFreeAtLevelIso n q X E).hom ≫ structureMap (shiftedHom n X E) p q := by
  have h := structureMap_hom (internalHomShiftIso n X E).hom p q
  change _ = PointedObject.smashMap (𝟙 (spherePower.{u} p))
    ((internalHomShiftIso n X E).hom.hom.app (FiniteBijection.of q)) ≫ _ at h
  simpa only [internalHomShiftIso_hom_app] using h

/-- 各段の比較は円による懸垂構造射とも両立する。 -/
lemma internalHomFreeAtLevelIso_suspensionMap (n q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    suspensionMap (internalHom ((freeAt n).obj X) E) q ≫
        (internalHomFreeAtLevelIso n (q + 1) X E).hom =
      PointedObject.smashMap (𝟙 (circle : PointedSimplicialSet.{u}))
        (internalHomFreeAtLevelIso n q X E).hom ≫ suspensionMap (shiftedHom n X E) q := by
  have h := suspensionMap_hom (internalHomShiftIso n X E).hom q
  simpa only [internalHomShiftIso_hom_app] using h

/-- 次数をずらした内部Homからの評価。 -/
def shiftedHomEvaluation (n : ℕ) (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    (SymmetricSequence.freeAt n).obj X ⊗ (shiftedHom n X E).X ⟶ E.X :=
  MonoidalModuleInternalHom.transportedEvaluation (C := PointedSymmetricSequence.{u})
    sphereSequence.{u} ((SymmetricSequence.freeAt n).obj X) E (homBySequenceShiftIso n X E)

/-- 次数をずらした内部Homの構造射は、各段の比較で元の構造射を移した射。 -/
lemma shiftedHom_structureMap (n p q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    structureMap (shiftedHom n X E) p q =
      PointedObject.smashMap (𝟙 (spherePower.{u} p)) (internalHomFreeAtLevelIso n q X E).inv ≫
        structureMap (internalHom ((freeAt n).obj X) E) p q ≫
          (internalHomFreeAtLevelIso n (p + q) X E).hom := by
  have h := structureMap_hom (internalHomShiftIso n X E).inv p q
  change _ = PointedObject.smashMap (𝟙 (spherePower.{u} p))
    ((internalHomShiftIso n X E).inv.hom.app (FiniteBijection.of q)) ≫ _ at h
  rw [internalHomShiftIso_inv_app, internalHomShiftIso_inv_app] at h
  have h' := congrArg (fun k => k ≫ (internalHomFreeAtLevelIso n (p + q) X E).hom) h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'

/-- 次数をずらした内部Homの懸垂構造射も各段の比較による移送で計算できる。 -/
lemma shiftedHom_suspensionMap (n q : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    suspensionMap (shiftedHom n X E) q =
      PointedObject.smashMap (𝟙 (circle : PointedSimplicialSet.{u}))
        (internalHomFreeAtLevelIso n q X E).inv ≫
          suspensionMap (internalHom ((freeAt n).obj X) E) q ≫
            (internalHomFreeAtLevelIso n (q + 1) X E).hom := by
  have h := suspensionMap_hom (internalHomShiftIso n X E).inv q
  rw [internalHomShiftIso_inv_app, internalHomShiftIso_inv_app] at h
  have h' := congrArg (fun k => k ≫ (internalHomFreeAtLevelIso n (q + 1) X E).hom) h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'

end SerrePositivity.SymmetricSpectrum
