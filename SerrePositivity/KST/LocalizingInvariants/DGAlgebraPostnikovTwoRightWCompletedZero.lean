module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWCompletedPath

/-!
概要：完成模型の零 class 経路を、W の反転と始点零経路の合成に同定する。
方針：係数復元・輸送・反転合成の全射を同じ零底へ写す。
規約：指定した完成模型の全 path を保持。使われ方：movingSourceNativeModelHomotopy の k₁。
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
local notation "α" => SquareZeroExtension.relativeLeft
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "β" => SquareZeroExtension.relativeRight
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "K" => d.rightClassifyingLayer R
local notation "a" => d.rightImageClass R
local notation "V" => postnikov R (B.obj j).obj 1
local notation "N" => postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1
local notation "N₀" => DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1
local notation "q" => postnikovTransition R (B.obj j).obj 1 0 (by omega)
local notation "z" => postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1
local notation "b" => postnikovCommonRightClassifyingBase R f
  d.baseInverse d.layerInverse d.target_le
local notation "q₀" => β ≫ b
local notation "u" => d.fixedRightFollowingWitness R
local notation "k" => SquareZero.baseChangeMap b N₀
local notation "hk" => SquareZero.baseChangeMap_projection b N₀

def rightOriginalCoefficientZeroNullPath :=
  ((SquareZeroExtension.relativeWitness K a).mapOver b k hk).rebase
    (q' := q₀) (by
      rw [d.rightImageClass_projection R]
      change (α ≫ d.classProjection R) ≫ b = _
      rw [← d.rightImageRelativeRight R])

lemma rightOriginalCoefficientZeroNullPath_hom :
    (d.rightOriginalCoefficientZeroNullPath R).hom = (d.rightOriginalZeroNullPath R).hom := by
  change SquareZeroExtension.relativePath K a ≫ Path.map R k =
    (SquareZeroExtension.relativePath K a ≫ Path.map R (d.rightImageClassRestore R)) ≫
      Path.map R z
  rw [Category.assoc, ← Path.map_comp, d.rightImageClassRestore_zero R]

lemma rightWCompletedNativePath_zeroClass : (d.rightWCompletedNativePath R).hom ≫
    Path.map R z =
    ((d.rightWZeroSourcePath R).reverse.comp (d.rightWInitialZeroPath R)).hom := by
  have ht : SquareZeroExtension.transport K (u) ≫
      SquareZeroExtension.relativePath K (d.fixedRightCompletedClass R) =
        (SquareZeroExtension.transportWitness K (u)).hom :=
    SquareZeroExtension.transport_path K (u)
  have hpath : (d.rightWCompletedNativePath R).hom ≫ Path.map R z =
      (SquareZeroExtension.transportWitness K (u)).hom ≫ Path.map R k := by
    change (d.rightWCompletedModel R ≫ HomotopyPullbackModel.path R _ _) ≫ Path.map R z = _
    conv_lhs =>
      rw [d.rightWCompletedModel_path R, Category.assoc, ← Path.map_comp,
        d.rightDenominatorClassRestore_zero R]
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ Path.map R k) ht)
  refine hpath.trans ?_
  let p := (SquareZeroExtension.relativeWitness K a).rebase
    (q' := α ≫ d.classProjection R) (by rw [d.rightImageClass_projection R])
  have hc := SquareZero.RelativeWitness.mapOver_comp_hom b k hk ((u).precomp α).reverse p
  have hr := SquareZero.RelativeWitness.mapOver_reverse_hom b k hk ((u).precomp α)
  have hf : (((u).precomp α).mapOver b k hk).hom = (d.rightFollowingZeroPath R).hom := rfl
  have hv := hr.trans (SquareZero.RelativeWitness.reverse_congr_hom_of_paths hf)
  have hp : (p.mapOver b k hk).hom = (d.rightOriginalZeroNullPath R).hom :=
    d.rightOriginalCoefficientZeroNullPath_hom R
  have he := SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v' := (d.rightFollowingZeroPath R).reverse)
    (w' := d.rightOriginalZeroNullPath R) hv hp
  exact hc.trans (he.trans (d.rightWZeroNull_composite R))

lemma rightWCompletedNativePath_nativeClass : (d.rightWCompletedNativePath R).hom ≫
    Path.map R ((postnikovNativeZeroIso R (B.obj j).obj 1 (by omega) 1).hom ≫
      SquareZero.baseChangeMap q N₀) =
    ((d.rightWZeroSourcePath R).reverse.comp (d.rightWInitialZeroPath R)).hom := by
  rw [postnikovNativeZeroIso_map]
  exact d.rightWCompletedNativePath_zeroClass R

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
