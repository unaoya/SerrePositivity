module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedUpperRightRoofPath

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
    Function.Surjective ((r).denominator.hom.f n) := by
  have := (r).denominator_epi
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

def fixedLeftCellLift : cellResolution R Aₖ ⟶ (r).apex :=
  cellResolutionMapLift R fₖ (r).denominator
    (d.nonpositiveFixedRightRoof_denominator_surjective R) (r).denominator_quasiIso

lemma fixedLeftCellLift_denominator : d.fixedLeftCellLift R ≫ (r).denominator =
    cellAugmentation R Aₖ ≫ fₖ := cellResolutionMapLift_projection R _ _ _ _

def fixedLeftDefectAfterF : Path.Witness R
    ((d.fixedLeftCellLift R ≫ (r).numerator) ≫ fⱼ)
    ((cellAugmentation R Aₖ ≫ a) ≫ fⱼ) := by
  let w := (d.nonpositiveFixedRightRoofPath R).precomp (d.fixedLeftCellLift R)
  refine ⟨w.hom, w.source_eq.trans (Category.assoc _ _ _).symm, ?_⟩
  refine w.target_eq.trans ?_
  rw [← Category.assoc, d.fixedLeftCellLift_denominator R]
  have hn := (f.map (postnikovFunctor R 2)).naturality hkj
  change (cellAugmentation R Aₖ ≫ (postnikovFunctor R 2).map (f.app k)) ≫
      (postnikovFunctor R 2).map (B.transition hkj) =
    (cellAugmentation R Aₖ ≫ (postnikovFunctor R 2).map (A.transition hkj)) ≫
      (postnikovFunctor R 2).map (f.app j)
  simp only [Category.assoc]
  exact congrArg (fun t => cellAugmentation R Aₖ ≫ t) hn.symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
