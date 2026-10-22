module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightStandardClass
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenStandard
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionComposition

/-!
概要：元の共通底上の右 class 標的を、B の零底平方零標的へ写す。
方針：元の零底射の合成と制限合成同型を使い、恒等係数の shift を保つ。
規約：分子・分母側の元の底射への合成式を保持。使われ方：class 経路の共通標的。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

local instance rightZero_apex_nonpositive : (postnikovCommonClassBase R f c d).X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof_nonpositive
local instance rightZero_target_lowerBound : (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

def postnikovCommonRightZeroBase : postnikovCommonClassBase R f c d ⟶
    postnikov R (B.obj i).obj 0 :=
  postnikovQuotient R (postnikovCommonClassBase R f c d) 0 ≫
    (postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c d.zero.source_le) ≫
      postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 0)

lemma postnikovCommonRightZeroBase_num : postnikovCommonRightZeroBase R f c d =
    postnikovCommonRightBase R f c d ≫ postnikovTransition R (B.obj i).obj 1 0 (by omega) :=
  (congrArg (fun t => postnikovQuotient R (postnikovCommonClassBase R f c d) 0 ≫ t)
    (postnikovCommonRightBase_zero R f c d).symm).trans (postnikovQuotient_desc R 0 _)

lemma postnikovCommonRightZeroBase_den : postnikovCommonRightZeroBase R f c d =
    postnikovCommonRightDenBase R f c d ≫ postnikovTransition R (B.obj i).obj 1 0 (by omega) :=
  (congrArg (fun t => postnikovQuotient R (postnikovCommonClassBase R f c d) 0 ≫ t)
    (postnikovCommonRightDenBase_zero R f c d).symm).trans (postnikovQuotient_desc R 0 _)

def postnikovCommonRightZeroLayerIso :
    bimoduleRestrict (postnikovCommonRightZeroBase R f c d)
      (postnikovLayerZeroBimodule R (B.obj i).obj 1) ≅ postnikovCommonRightLayer R f c d :=
  bimoduleRestrictionCompIso _ _ _

def postnikovCommonRightZeroCoefficient :
    DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) 1 ⟶
      bimoduleRestrict (postnikovCommonRightZeroBase R f c d)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1) :=
  DGBimoduleShift.mapOver _ _ 1 (postnikovCommonRightZeroLayerIso R f c d).inv

lemma postnikovCommonRightZeroCoefficient_hom :
    (postnikovCommonRightZeroCoefficient R f c d).hom =
      𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦(1 : ℤ)⟧) := by
  rw [postnikovCommonRightZeroCoefficient, DGBimoduleShift.mapOver_hom]
  have he : (postnikovCommonRightZeroLayerIso R f c d).inv.hom =
      𝟙 (postnikovLayer R (B.obj i).obj 1) := rfl
  rw [he]
  change (shiftFunctor (Complex R) (1 : ℤ)).map (𝟙 (postnikovLayer R (B.obj i).obj 1)) = 𝟙 _
  exact (shiftFunctor (Complex R) (1 : ℤ)).map_id _

def postnikovCommonRightClassToZero : postnikovCommonRightClassTarget R f c d ⟶
    postnikovZeroClassTarget R (B.obj i).obj 1 1 :=
  SquareZero.mapOver _ _ _ (postnikovCommonRightZeroCoefficient R f c d)

lemma postnikovCommonRightClassToZero_projection : postnikovCommonRightClassToZero R f c d ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ ≫ postnikovCommonRightZeroBase R f c d :=
  SquareZero.mapOver_projection _ _ _ _

lemma postnikovCommonRightClassToZero_hom : (postnikovCommonRightClassToZero R f c d).hom =
    biprod.map (postnikovCommonRightZeroBase R f c d).hom
      (𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦(1 : ℤ)⟧)) := by
  change biprod.map (postnikovCommonRightZeroBase R f c d).hom
    (postnikovCommonRightZeroCoefficient R f c d).hom = _
  rw [postnikovCommonRightZeroCoefficient_hom]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
