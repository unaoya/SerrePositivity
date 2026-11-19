module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHomFree
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomFree

/-! # 自由原変数の内部Hom比較の自然性と作用の評価公式

通常の内部Homの前合成・後合成を、球面作用と両立するスペクトル射へ持ち上げる。
作用の評価公式は共通層のfreeHomObj_action_evaluationで公開する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.PointedSimplicialSet

/-- 対称列に反変、スペクトルに共変の通常の内部Homのスペクトル射。 -/
abbrev homBySequenceMap {X Y : PointedSymmetricSequence.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) : homBySequence Y E ⟶ homBySequence X F :=
  MonoidalModuleInternalHom.freeHomMap
    (C := PointedSymmetricSequence.{u}) sphereSequence.{u} f g

/-- 自由原変数のスペクトル比較は両変数に関して自然。 -/
@[reassoc]
lemma internalHomFreeIso_naturality {X Y : PointedSymmetricSequence.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    internalHomMap (freeFunctor.map f) g ≫ (internalHomFreeIso X F).hom =
      (internalHomFreeIso Y E).hom ≫ homBySequenceMap f g :=
  MonoidalModuleInternalHom.freeHomModuleIso_naturality
    (C := PointedSymmetricSequence.{u}) sphereSequence.{u} f g

/-- F_nを原変数に置く内部Homの比較も両変数に関して自然。 -/
@[reassoc]
lemma internalHomFreeAtIso_naturality (n : ℕ) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    internalHomMap ((freeAt n).map f) g ≫ (internalHomFreeAtIso n X F).hom =
      (internalHomFreeAtIso n Y E).hom ≫ homBySequenceMap ((SymmetricSequence.freeAt n).map f) g := by
  unfold internalHomFreeAtIso
  dsimp only [freeAt, GeneralSymmetricSpectrum.freeAt, Functor.comp_map, Functor.comp_obj]
  apply internalHomFreeIso_naturality

end SerrePositivity.SymmetricSpectrum
