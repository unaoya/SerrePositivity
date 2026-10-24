module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightWSource
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeNullComposition

/-!
概要：fⱼ 自然性の終点の零経路と、W の全 class 経路を同じ零底に揃える。
方針：元の native 零経路を affine 輸送し、動く底の始点と零切断の式で照合する。
規約：零経路と全 W 経路を実構成する。使われ方：native 模型経路の a₀・v・p 入力。
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
local notation "α" => SquareZeroExtension.relativeLeft
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "β" => SquareZeroExtension.relativeRight
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "V" => postnikov R (B.obj j).obj n
local notation "V₀" => postnikov R (B.obj j).obj 0
local notation "N" => postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1
local notation "N₀" => DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1
local notation "E" => postnikovPerturbedExtension R (B.obj j).obj n hn
local notation "C" => postnikovPerturbedClass R (B.obj j).obj n hn
local notation "q" => postnikovTransition R (B.obj j).obj n 0 (by omega)
local notation "z" => postnikovClassToZeroBase R (B.obj j).obj n hn 1
local notation "r" => d.rightWBasePath R
local notation "q₀" => β ≫ PostnikovCommonCore.postnikovCommonRightClassifyingBase R hn f
  d.baseInverse d.layerInverse d.target_le
local notation "l₀" => α ≫ ((PostnikovCommonCore.postnikovCommonRightGammaSourceWitness R hn f
  d.baseInverse d.layerInverse d.target_le).hom ≫ Path.source R E)
local notation "l₁" => α ≫ d.fixedRightCompletedNativeSource R

def rightGammaNativeNullPath :=
  (SquareZeroExtension.sourceModelClassWitness N C
    (β ≫ PostnikovCommonCore.postnikovCommonClassRightImageBase R hn f d.baseInverse d.layerInverse d.target_le)
    (d.rightImageModelSourcePath R) (d.rightImageModelSourcePath_relative R)).reverse.comp
      (d.rightImageNativeNullPath R)

def rightWInitialNativePath : SquareZero.RelativeWitness (r ≫ Path.source R V) N
    (l₀ ≫ C) ((r ≫ Path.source R V) ≫ SquareZero.zeroSection V N) where
  hom := (d.rightGammaNativeNullPath R).hom
  source_eq := (d.rightGammaNativeNullPath R).source_eq
  target_eq := (d.rightGammaNativeNullPath R).target_eq.trans
    (congrArg (fun t => t ≫ SquareZero.zeroSection V N) (d.rightWBasePath_source R).symm)
  projection_eq := (d.rightGammaNativeNullPath R).projection_eq.trans
    (congrArg (fun t => t ≫ Path.diagonal R V) (d.rightWBasePath_source R).symm)

lemma rightWZeroBase_source : (r ≫ Path.source R V) ≫ q = q₀ := by
  rw [d.rightWBasePath_source R, Category.assoc, PostnikovCommonCore.postnikovCommonClassRightImageBase_zero]

def rightWZeroSourcePath : SquareZero.RelativeWitness q₀ N₀
    ((l₀ ≫ C) ≫ z) ((l₁ ≫ C) ≫ z) where
  toWitness := ((d.rightWSourcePath R).postcomp C).postcomp z
  projection_eq := by
    change (((d.rightWSourcePath R).hom ≫ Path.map R C) ≫ Path.map R z) ≫ _ = _
    rw [Category.assoc, ← Path.map_comp, postnikovClassToZeroBase_projection,
      Path.map_comp, ← Category.assoc, d.rightWClass_projection R, d.rightWBasePath_zero R]

def rightWInitialZeroPath : SquareZero.RelativeWitness q₀ N₀
    ((l₀ ≫ C) ≫ z) (q₀ ≫ SquareZero.zeroSection V₀ N₀) where
  hom := (d.rightWInitialNativePath R).hom ≫ Path.map R z
  source_eq := ((d.rightWInitialNativePath R).toWitness.postcomp z).source_eq
  target_eq := by
    refine ((d.rightWInitialNativePath R).toWitness.postcomp z).target_eq.trans ?_
    rw [Category.assoc]
    change (r ≫ Path.source R V) ≫
      (SquareZero.zeroSection V N ≫ SquareZero.mapOver q N N₀
        (postnikovShiftedLayerToZeroBase R (B.obj j).obj n hn 1)) = _
    rw [SquareZero.zeroSection_mapOver, ← Category.assoc, d.rightWZeroBase_source R]
  projection_eq := by
    have h := ((d.rightWInitialNativePath R).mapOver q z
      (postnikovClassToZeroBase_projection R (B.obj j).obj n hn 1)).projection_eq
    exact h.trans (congrArg (fun t => t ≫ Path.diagonal R V₀) (d.rightWZeroBase_source R))

lemma rightWSource_nativeClass : ((d.rightWSourcePath R).hom ≫ Path.map R C) ≫
    Path.map R ((postnikovNativeZeroIso R (B.obj j).obj n hn 1).hom ≫
      SquareZero.baseChangeMap q N₀) = (d.rightWZeroSourcePath R).hom := by
  rw [postnikovNativeZeroIso_map]
  rfl

lemma rightWInitial_nativeClass : (d.rightWInitialNativePath R).hom ≫
    Path.map R ((postnikovNativeZeroIso R (B.obj j).obj n hn 1).hom ≫
      SquareZero.baseChangeMap q N₀) = (d.rightWInitialZeroPath R).hom := by
  rw [postnikovNativeZeroIso_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
