module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWInitialPath

/-!
概要：fⱼ 自然性・W・元の零経路を同じ零底で比較し、後続輸送の全経路を回収する。
方針：元の全 class 像と affine 反転・合成の保存則を使う。
規約：経路の端点一致だけでは比較しない。使われ方：native 模型の k₁ 入力。
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
local notation "V" => postnikov R (B.obj j).obj 1
local notation "V₀" => postnikov R (B.obj j).obj 0
local notation "N" => postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1
local notation "N₀" => DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1
local notation "C" => postnikovPerturbedClass R (B.obj j).obj 1 (by omega)
local notation "q" => postnikovTransition R (B.obj j).obj 1 0 (by omega)
local notation "z" => postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1
local notation "b" => postnikovCommonRightClassifyingBase R f
  d.baseInverse d.layerInverse d.target_le
local notation "q₀" => β ≫ b
local notation "vₙ" => SquareZeroExtension.sourceModelClassWitness N C
  (β ≫ postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
  (d.rightImageModelSourcePath R) (d.rightImageModelSourcePath_relative R)
local notation "v₀" => postnikovCommonClassFixedRightNaturality R f
  d.baseInverse d.layerInverse d.target_le
local notation "w₀" => postnikovCommonClassFixedRightBottom R f
  d.baseInverse d.layerInverse d.target_le d.inverse

def rightNatZeroSourcePath :=
  ((vₙ).mapOver q z (postnikovClassToZeroBase_projection R (B.obj j).obj 1 (by omega) 1)).rebase
    (q' := q₀) (by rw [Category.assoc, postnikovCommonClassRightImageBase_zero])

def rightOriginalZeroNullPath :=
  ((d.rightImageNativeNullPath R).mapOver q z
    (postnikovClassToZeroBase_projection R (B.obj j).obj 1 (by omega) 1)).rebase
      (q' := q₀) (by rw [Category.assoc, postnikovCommonClassRightImageBase_zero])

lemma rightNatZeroSourcePath_hom : (d.rightNatZeroSourcePath R).hom = α ≫ (v₀).hom := by
  change ((α ≫ (d.rightImageSourcePath R).hom) ≫ Path.map R C) ≫ Path.map R z = _
  calc
    _ = α ≫ (((d.rightImageSourcePath R).hom ≫ Path.map R C) ≫ Path.map R z) := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun t => α ≫ t) (d.rightImageSourcePath_zeroClass R)

lemma rightWZeroSourcePath_hom : (d.rightWZeroSourcePath R).hom = α ≫ (w₀).hom := by
  change ((α ≫ (postnikovCommonRightGammaSourceWitness R f
    d.baseInverse d.layerInverse d.target_le).hom) ≫ Path.map R C) ≫ Path.map R z =
      α ≫ ((postnikovCommonRightContourBottomRefinedPath R f d.baseInverse
        d.layerInverse d.target_le).hom ≫ Path.map R (SquareZero.baseChangeMap b N₀))
  have h := congrArg (fun t => α ≫ t)
    (postnikovCommonRightGammaSourceWitness_zeroClass R f d.baseInverse d.layerInverse d.target_le)
  simpa only [Category.assoc] using h

def rightFollowingZeroRawPath :=
  (((d.fixedRightFollowingWitness R).precomp α).mapOver b (SquareZero.baseChangeMap b N₀)
    (SquareZero.baseChangeMap_projection b N₀)).rebase
      (q' := q₀) (by
        change (α ≫ d.classProjection R) ≫ b = _
        rw [← d.rightImageRelativeRight R])

lemma rightFollowingZeroRawPath_hom : (d.rightFollowingZeroRawPath R).hom =
    ((d.rightNatZeroSourcePath R).comp (d.rightWZeroSourcePath R)).hom := by
  change (α ≫ (d.fixedRightFollowingWitness R).hom) ≫ Path.map R _ = _
  have hf := congrArg (fun t => α ≫ t) (d.fixedRightFollowingWitness_zero_map R)
  have hc := SquareZero.RelativeWitness.precomp_comp_hom (v₀) (w₀) α
  have he := SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v := (v₀).precomp α) (w := (w₀).precomp α)
    (v' := d.rightNatZeroSourcePath R) (w' := d.rightWZeroSourcePath R)
    (d.rightNatZeroSourcePath_hom R).symm (d.rightWZeroSourcePath_hom R).symm
  exact (Category.assoc _ _ _).trans (hf.trans (hc.trans he))

def rightFollowingZeroPath :=
  ((d.rightNatZeroSourcePath R).comp (d.rightWZeroSourcePath R)).replaceHom
    (d.rightFollowingZeroRawPath R).hom (d.rightFollowingZeroRawPath_hom R).symm

lemma rightFollowingZeroPath_hom : (d.rightFollowingZeroPath R).hom =
    ((d.rightNatZeroSourcePath R).comp (d.rightWZeroSourcePath R)).hom :=
  d.rightFollowingZeroRawPath_hom R

lemma rightWInitialZeroPath_nested : (d.rightWInitialZeroPath R).hom =
    ((d.rightNatZeroSourcePath R).reverse.comp (d.rightOriginalZeroNullPath R)).hom := by
  have hc := SquareZero.RelativeWitness.mapOver_comp_hom q z
    (postnikovClassToZeroBase_projection R (B.obj j).obj 1 (by omega) 1)
    (vₙ).reverse (d.rightImageNativeNullPath R)
  have hr := SquareZero.RelativeWitness.mapOver_reverse_hom q z
    (postnikovClassToZeroBase_projection R (B.obj j).obj 1 (by omega) 1) (vₙ)
  exact hc.trans (SquareZero.RelativeWitness.comp_congr_hom_of_paths hr rfl)

lemma rightWZeroNull_composite :
    ((d.rightFollowingZeroPath R).reverse.comp (d.rightOriginalZeroNullPath R)).hom =
    ((d.rightWZeroSourcePath R).reverse.comp (d.rightWInitialZeroPath R)).hom := by
  have h := SquareZero.RelativeWitness.reverse_congr_hom_of_paths (d.rightFollowingZeroPath_hom R)
  have hc := SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v := (d.rightFollowingZeroPath R).reverse)
    (v' := ((d.rightNatZeroSourcePath R).comp (d.rightWZeroSourcePath R)).reverse)
    (w := d.rightOriginalZeroNullPath R) (w' := d.rightOriginalZeroNullPath R) h rfl
  have ha := SquareZero.RelativeWitness.reverse_comp_null_hom
    (d.rightNatZeroSourcePath R) (d.rightWZeroSourcePath R) (d.rightOriginalZeroNullPath R)
  exact hc.trans (ha.trans (SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v := (d.rightWZeroSourcePath R).reverse) (v' := (d.rightWZeroSourcePath R).reverse)
    (w := (d.rightNatZeroSourcePath R).reverse.comp (d.rightOriginalZeroNullPath R))
    (w' := d.rightWInitialZeroPath R) rfl (d.rightWInitialZeroPath_nested R).symm))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
