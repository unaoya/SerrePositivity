module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteDerivedPro
public import Mathlib.CategoryTheory.Localization.Construction

/-!
概要：実 dg 代数の準同型局所化を作り、有限 Postnikov 切断の元の塔の pro 同型を供給。
方針：通常圏の射の形式的反転を使い、実 roof による切断比較を適用する。
規約：D の加群・Perf と別の代数の通常局所化。一般 pro ∞ 圏との同定は未提供。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R]

def quasiIsoProperty : MorphismProperty (Mon (Complex R)) := fun _ _ f => QuasiIso f.hom

abbrev QuasiIsoLocalization := (quasiIsoProperty R).Localization

def quasiIsoLocalization : Mon (Complex R) ⥤ QuasiIsoLocalization R := (quasiIsoProperty R).Q

lemma quasiIsoLocalization_inverts : InvertsQuasiIsos R (quasiIsoLocalization R) :=
  fun f hf => (quasiIsoProperty R).Q_inverts f hf

lemma postnikovQuasiIsoLocalization_isProIso_finite (A : Tower (NonpositiveAlgebra R))
    (b : ℤ) (hb : 0 ≤ b) (a : ℤ) (hab : b ≤ a)
    (hA : ∀ j : ℤ, b < j → j ≤ a →
      IsProZero ((A.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso ((postnikovTransitionLevelHom R A a b hab).map (quasiIsoLocalization R)) :=
  postnikovTransitionLevelHom_isProIso_finite R A (quasiIsoLocalization R)
    (quasiIsoLocalization_inverts R) b hb a hab hA

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
