module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightRoofPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoofPrecomposePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofConjugationPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoof

/-!
概要：fixed class roof の実右三角形を、元の次段切断代数と非正次数 roof へ戻す。
方針：源の準同型逆・元の上下段比較・cell 経路反映・connective cover を順に使う。
規約：値の三角形や H⁻⁽ⁿ⁺¹⁾ の三角形で代用しない。使われ方：NonpositiveInverseRoof の右経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

set_option quotPrecheck false
local notation "a" => postnikovHomotopyPullbackComparison R (A.obj j).obj n hn
local notation "b" => postnikovHomotopyPullbackComparison R
  (B.obj d.layerInverse.zero.stage).obj n hn
local notation "c" => postnikovHomotopyPullbackComparison R (B.obj j).obj n hn
local notation "ha" => postnikovHomotopyPullbackComparison_quasiIso R (A.obj j).obj n hn
local notation "hc" => postnikovHomotopyPullbackComparison_quasiIso R (B.obj j).obj n hn
local notation "f₂" => postnikovMap R (f.app j).hom (n + 1)
local notation "fₘ" => postnikovClassModelMap R n hn (f.app j).hom
local notation "t" => PostnikovCommonCore.postnikovCommonRightDenDirectMap R hn f
  d.baseInverse d.layerInverse d.target_le
local notation "t₂" => postnikovMap R t (n + 1)
local notation "tₘ" => postnikovClassModelMap R n hn t

abbrev rightSourceClassRoof :=
  ((SurjectiveRoof.ofQuasiIsoInverse R (d.sourceToOriginalModel R)
    (d.sourceToOriginalModel_quasiIso R)).comp R (d.classModelFixedRightRoof R)).cellRefinement R 1

def rightSourceClassRoofPath : Path.Witness R
    ((d.rightSourceClassRoof R).numerator ≫ fₘ)
    ((d.rightSourceClassRoof R).denominator ≫ tₘ) :=
  SurjectiveRoof.inversePrecomposeRightPath R (d.sourceToOriginalModel R)
    (d.sourceToOriginalModel_quasiIso R) (d.classModelFixedRightRoof R) fₘ tₘ
    (d.classModelFixedRightRoofPath R)

abbrev upperFixedRightRawRoof := RoofConjugation.roof R (d.rightSourceClassRoof R) b a ha

def upperFixedRightAfterComparison := RoofConjugation.rightPathAfterComparison R
  (d.rightSourceClassRoof R) b a ha f₂ fₘ c t₂ tₘ
  (postnikovHomotopyPullbackComparison_square R n hn (f.app j).hom)
  (postnikovHomotopyPullbackComparison_square R n hn t).symm
  (d.rightSourceClassRoofPath R)

abbrev upperFixedRightRoof :=
  ((d.upperFixedRightRawRoof R).cellRefinement R 1).cellRefinement R 4

def upperFixedRightRoofPath : Path.Witness R
    ((d.upperFixedRightRoof R).numerator ≫ f₂)
    ((d.upperFixedRightRoof R).denominator ≫ t₂) := by
  let h := d.upperFixedRightAfterComparison R
  let h' : Path.Witness R
      ((((d.upperFixedRightRawRoof R).cellRefinement R 1).numerator ≫ f₂) ≫ c)
      ((((d.upperFixedRightRawRoof R).cellRefinement R 1).denominator ≫ t₂) ≫ c) :=
    { hom := h.hom
      source_eq := h.source_eq.trans (Category.assoc _ _ _).symm
      target_eq := h.target_eq.trans (Category.assoc _ _ _).symm }
  exact SurjectiveRoof.cellReflectEquation R ((d.upperFixedRightRawRoof R).cellRefinement R 1)
    f₂ t₂ c hc h'

abbrev nonpositiveFixedRightRoof := (d.upperFixedRightRoof R).nonpositiveNormalization R

lemma nonpositiveFixedRightRoof_nonpositive : (d.nonpositiveFixedRightRoof R).apex.X.IsStrictlyLE 0 :=
  SurjectiveRoof.nonpositiveNormalization_apex R _

def nonpositiveFixedRightRoofPath : Path.Witness R
    ((d.nonpositiveFixedRightRoof R).numerator ≫ f₂)
    ((d.nonpositiveFixedRightRoof R).denominator ≫ t₂) := by
  let h := (d.upperFixedRightRoofPath R).precomp
    (connectiveCoverInclusion R (d.upperFixedRightRoof R).apex)
  exact { hom := h.hom
          source_eq := h.source_eq.trans (Category.assoc _ _ _).symm
          target_eq := h.target_eq.trans (Category.assoc _ _ _).symm }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
