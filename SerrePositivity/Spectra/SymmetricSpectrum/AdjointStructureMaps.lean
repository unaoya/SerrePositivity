module

public import SerrePositivity.Spectra.SymmetricSpectrum.Suspension
public import SerrePositivity.Spectra.SymmetricSpectrum.SuspensionLoop

/-! # 懸垂構造射の通常の内部Homへの随伴表示 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.PointedSimplicialSet

/-- 円とのsmashの構造射を、次の段からの通常のループへの射へ転置する。 -/
def adjointStructureMap (E : SymmetricSpectrum.{u}) (n : ℕ) :
    level E n ⟶ (ihom (circle : PointedSimplicialSet.{u})).obj (level E (n + 1)) :=
  curry (suspensionMap E n)

/-- スペクトル射は構造射の随伴表示とも両立する。 -/
@[reassoc]
lemma adjointStructureMap_naturality {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) (n : ℕ) :
    f.hom.app (FiniteBijection.of n) ≫ adjointStructureMap F n =
      adjointStructureMap E n ≫
        (ihom (circle : PointedSimplicialSet.{u})).map
          (f.hom.app (FiniteBijection.of (n + 1))) := by
  have h := congrArg (fun g => curry g) (suspensionMap_hom f n)
  change curry (suspensionMap E n ≫ f.hom.app (FiniteBijection.of (n + 1))) =
    curry ((circle : PointedSimplicialSet.{u}) ◁ f.hom.app (FiniteBijection.of n) ≫
      suspensionMap F n) at h
  rw [curry_natural_right, curry_natural_left] at h
  exact h.symm

end SerrePositivity.SymmetricSpectrum
