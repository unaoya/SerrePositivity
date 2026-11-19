module

public import SerrePositivity.Spectra.General.Free
public import SerrePositivity.Spectra.SymmetricSpectrum.Sphere

/-! # 自由な円周スペクトル

自由加群関手と生成元は一般の構成を使う。作用を球面の乗法で書く公式と延長の一意性を記す。
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action)
open SerrePositivity.PointedSimplicialSet
/-- 対称列Fを生成元とする自由球面加群。 -/
abbrev freeObj := GeneralSymmetricSpectrum.freeObj circle.{u}
/-- 対称列から自由対称スペクトルを作る関手。 -/
abbrev freeFunctor := GeneralSymmetricSpectrum.freeFunctor circle.{u}
/-- 対称列から自由対称スペクトルへの生成元の射。 -/
abbrev generator := GeneralSymmetricSpectrum.generator circle.{u}
/-- 自由対称スペクトルの作用は球面の乗法から得る射。 -/
lemma free_action (F : PointedSymmetricSequence.{u}) :
    action (freeObj F) = (α_ sphereSequence.{u} sphereSequence.{u} F).inv ≫
      (sphereMultiplication.{u} ▷ F) := rfl
/-- 生成元で指定した値を持つスペクトルの射は一意。 -/
lemma lift_unique {F : PointedSymmetricSequence.{u}} (E : SymmetricSpectrum.{u})
    (f : freeObj F ⟶ E) (g : F ⟶ E.X) (h : generator F ≫ f.hom = g) :
    f = GeneralSymmetricSpectrum.lift circle E g := by
  apply (GeneralSymmetricSpectrum.freeHomEquiv circle F E).injective
  exact h.trans (GeneralSymmetricSpectrum.generator_lift circle E g).symm
/-- 自由スペクトルの作用を忘れると球面との左convolutionになる。 -/
lemma free_forget_eq_tensorLeft :
    freeFunctor.{u} ⋙ forget.{u} = tensorLeft sphereSequence.{u} := rfl
end SerrePositivity.SymmetricSpectrum
