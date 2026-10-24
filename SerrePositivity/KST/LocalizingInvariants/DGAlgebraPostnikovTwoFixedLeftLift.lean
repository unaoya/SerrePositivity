module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedUpperRightRoofPath

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedLeftLift

/-!
概要：二切断の右逆 roof に元の源の cell 分解を持ち上げ、左三角形の残る経路を明示する。
方針：分母の全射準同型性で実 lift を作り、右経路と元の塔の自然性を前合成する。
規約：fⱼ の先の経路を元の左三角形とは扱わない。使われ方：左三角形の実反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

set_option quotPrecheck false
local notation "k" => d.layerInverse.zero.stage
local notation "hkj" => d.target_le.trans
  (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)
local notation "Aₖ" => postnikov R (A.obj k).obj 2
local notation "r" => d.nonpositiveFixedRightRoof R
local notation "fₖ" => postnikovMap R (f.app k).hom 2
local notation "fⱼ" => postnikovMap R (f.app j).hom 2
local notation "a" => postnikovMap R (A.transition hkj).hom 2

lemma nonpositiveFixedRightRoof_denominator_surjective (n : ℤ) :
    Function.Surjective ((r).denominator.hom.f n) :=
  PostnikovSuccessorClassInverseData.nonpositiveFixedRightRoof_denominator_surjective
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (degree := n)

def fixedLeftCellLift : cellResolution R Aₖ ⟶ (r).apex :=
  PostnikovSuccessorClassInverseData.fixedLeftCellLift
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedLeftCellLift_denominator : d.fixedLeftCellLift R ≫ (r).denominator =
    cellAugmentation R Aₖ ≫ fₖ :=
  PostnikovSuccessorClassInverseData.fixedLeftCellLift_denominator
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedLeftDefectAfterF : Path.Witness R
    ((d.fixedLeftCellLift R ≫ (r).numerator) ≫ fⱼ)
    ((cellAugmentation R Aₖ ≫ a) ≫ fⱼ) :=
  PostnikovSuccessorClassInverseData.fixedLeftDefectAfterF
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
