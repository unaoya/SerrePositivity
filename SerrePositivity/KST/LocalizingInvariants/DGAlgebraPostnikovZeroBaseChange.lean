module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackProProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoLocalization
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantTowers

/-!
概要：元の π₀ 群の pro 同型から、零切断を底に持つ元の経路模型の右射影を比較する。
方針：元の零代数の実逆を cospan の逆へ持ち上げ、局所化と元の不変量値へ送る。
規約：高次層の逆や一般 pro ∞ 同値は主張しない。使われ方：有限切断比較の底の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) (n : ℤ) (hn : 0 ≤ n)

/-- 元の零切断の射と標的の n 切断からの商射による実経路模型の塔。 -/
def postnikovZeroBaseTower : Tower (Mon (Complex R)) :=
  modelTower R (f.map (postnikovFunctor R 0)) (postnikovTransitionLevelHom R B n 0 hn)

/-- 元の経路模型から標的の n 切断への元の右射影。 -/
def postnikovZeroBaseProjection :
    LevelHom (postnikovZeroBaseTower R f n hn) (B.map (postnikovFunctor R n)) :=
  rightProjection R (f.map (postnikovFunctor R 0)) (postnikovTransitionLevelHom R B n 0 hn)

lemma postnikovZeroBaseProjection_localized_isProIso
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso ((postnikovZeroBaseProjection R f n hn).map (quasiIsoLocalization R)) :=
  rightProjection_isProIso_of_inverts R _ _ (quasiIsoLocalization R)
    (quasiIsoLocalization_inverts R) (postnikovZeroMap_isProIso R f hf)

variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

lemma IsKConnective.postnikovZeroBaseProjection_value_isProIso
    {k : ℤ} (h : IsKConnective R Φ k)
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso ((postnikovZeroBaseProjection R f n hn).map (invariantFunctor R Φ)) :=
  rightProjection_isProIso_of_connective R _ _ (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ)
    (fun i => postnikov_isConnective R (B.obj i).obj n) (postnikovZeroMap_isProIso R f hf)

lemma IsKConnective.postnikovZeroBaseProjection_value_piProEquivalence
    {k : ℤ} (h : IsKConnective R Φ k)
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    ProSpectrum.IsPiProEquivalence
      ((postnikovZeroBaseProjection R f n hn).map (invariantFunctor R Φ)) :=
  ProSpectrum.piProEquivalence_of_proIso
    (h.postnikovZeroBaseProjection_value_isProIso R f n hn Φ hf)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
