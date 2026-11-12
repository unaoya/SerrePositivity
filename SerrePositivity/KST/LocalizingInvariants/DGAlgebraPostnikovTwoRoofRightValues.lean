module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofRightTraces
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBaseChangeValues

/-!
概要：元の右乗法的経路に沿う二切断模型の比較を、実不変量値の同型へ移す。
方針：非正次数共通模型への実準同型を反転し、元の底と上段への射を保持する。
規約：分子・分母から共通模型への射を同型とは扱わない。使われ方：二切断の逆の貼合せ。
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
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

attribute [local instance] roof_nonpositive upper_nonpositive

def postnikovTwoRoofRightValueIso {k : ℤ} (h : IsKConnective R Φ k) :
    (invariantFunctor R Φ).obj (postnikovTwoRoofRightFirstModel R f c) ≅
      (invariantFunctor R Φ).obj (postnikovTwoRoofRightSecondModel R f c) :=
  PathBaseChange.valueIso R (postnikovTwoRoofRightFirst R f c)
    (postnikovTwoRoofRightSecond R f c)
    (postnikovTransition R (B.obj i).obj 2 1 (by omega))
    (postnikovTwoRoofRightWitness R f c) Φ h

lemma postnikovTwoRoofRightValueIso_base {k : ℤ} (h : IsKConnective R Φ k) :
    (postnikovTwoRoofRightValueIso R f c Φ h).hom ≫
      (invariantFunctor R Φ).map (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
        (postnikovTwoRoofRightSecond R f c)) =
    (invariantFunctor R Φ).map (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
      (postnikovTwoRoofRightFirst R f c)) :=
  PathBaseChange.valueIso_base R _ _ _ _ Φ h

lemma postnikovTwoRoofRightValueIso_upper {k : ℤ} (h : IsKConnective R Φ k) :
    (postnikovTwoRoofRightValueIso R f c Φ h).hom ≫
      (invariantFunctor R Φ).map (postnikovExtensionBaseChangeUpper R (B.obj i).obj 1
        (postnikovTwoRoofRightSecond R f c)) =
    (invariantFunctor R Φ).map (postnikovExtensionBaseChangeUpper R (B.obj i).obj 1
      (postnikovTwoRoofRightFirst R f c)) :=
  PathBaseChange.valueIso_upper R _ _ _ _ Φ h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
