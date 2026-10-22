module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

/-!
概要：二つの標準 class 標的から共通零標的への元の実射の可換式を証明する。
方針：恒等係数の同型と元の二つの底合成式を、対角直和の両射影で照合する。
規約：元の cell class と底変更を保持。使われ方：橋渡し経路の両端の正規化。
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

lemma postnikovCommonRightClassIso_matrix : (postnikovCommonRightClassIso R f c d).hom.hom =
    biprod.map (𝟙 (postnikovCommonClassBase R f c d).X)
      (𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦(1 : ℤ)⟧)) := by
  change biprod.map (𝟙 (postnikovCommonClassBase R f c d).X)
    (postnikovCommonRightShiftedBaseIso R f c d 1).hom.hom = _
  rw [postnikovCommonRightShiftedBaseIso_hom]
  rfl

lemma postnikovCommonRightDenClassIso_matrix : (postnikovCommonRightDenClassIso R f c d).hom.hom =
    biprod.map (𝟙 (postnikovCommonClassBase R f c d).X)
      (𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦(1 : ℤ)⟧)) := by
  change biprod.map (𝟙 (postnikovCommonClassBase R f c d).X)
    (postnikovCommonRightShiftedDenBaseIso R f c d 1).hom.hom = _
  rw [postnikovCommonRightShiftedDenBaseIso_hom]
  rfl

lemma postnikovCommonRightClassIso_zero : (postnikovCommonRightClassIso R f c d).hom ≫
    postnikovCommonRightClassToZero R f c d =
      SquareZero.baseChangeMap (postnikovCommonRightBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
      postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1 := by
  apply Mon.Hom.ext
  change (postnikovCommonRightClassIso R f c d).hom.hom ≫
    (postnikovCommonRightClassToZero R f c d).hom =
      (SquareZero.baseChangeMap (postnikovCommonRightBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1)).hom ≫
      (postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1).hom
  rw [postnikovCommonRightClassIso_matrix, postnikovCommonRightClassToZero_hom,
    SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom,
    congrArg Mon.Hom.hom (postnikovCommonRightZeroBase_num R f c d)]
  change biprod.map (𝟙 (postnikovCommonClassBase R f c d).X) (𝟙 _) ≫
      biprod.map ((postnikovCommonRightBase R f c d).hom ≫
        (postnikovTransition R (B.obj i).obj 1 0 (by omega)).hom) (𝟙 _) =
    biprod.map (postnikovCommonRightBase R f c d).hom (𝟙 _) ≫
      biprod.map (postnikovTransition R (B.obj i).obj 1 0 (by omega)).hom (𝟙 _)
  apply biprod.hom_ext <;> simp [Category.assoc]

lemma postnikovCommonRightDenClassIso_zero : (postnikovCommonRightDenClassIso R f c d).hom ≫
    postnikovCommonRightClassToZero R f c d =
      SquareZero.baseChangeMap (postnikovCommonRightDenBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
      postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1 := by
  apply Mon.Hom.ext
  change (postnikovCommonRightDenClassIso R f c d).hom.hom ≫
    (postnikovCommonRightClassToZero R f c d).hom =
      (SquareZero.baseChangeMap (postnikovCommonRightDenBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1)).hom ≫
      (postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1).hom
  rw [postnikovCommonRightDenClassIso_matrix, postnikovCommonRightClassToZero_hom,
    SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom,
    congrArg Mon.Hom.hom (postnikovCommonRightZeroBase_den R f c d)]
  change biprod.map (𝟙 (postnikovCommonClassBase R f c d).X) (𝟙 _) ≫
      biprod.map ((postnikovCommonRightDenBase R f c d).hom ≫
        (postnikovTransition R (B.obj i).obj 1 0 (by omega)).hom) (𝟙 _) =
    biprod.map (postnikovCommonRightDenBase R f c d).hom (𝟙 _) ≫
      biprod.map (postnikovTransition R (B.obj i).obj 1 0 (by omega)).hom (𝟙 _)
  apply biprod.hom_ext <;> simp [Category.assoc]

lemma postnikovCommonRightStandardClass_zero : postnikovCommonRightStandardClass R f c d ≫
    postnikovCommonRightClassToZero R f c d =
    (cellResolutionMap R (postnikovCommonRightBase R f c d) ≫
      postnikovCellClass R (B.obj i).obj 1 (by omega)) ≫
        postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1 := by
  rw [postnikovCommonRightStandardClass, Category.assoc, postnikovCommonRightClassIso_zero,
    ← Category.assoc, postnikovCellClassOver_map]

lemma postnikovCommonRightDenStandardClass_zero : postnikovCommonRightDenStandardClass R f c d ≫
    postnikovCommonRightClassToZero R f c d =
    (cellResolutionMap R (postnikovCommonRightDenBase R f c d) ≫
      postnikovCellClass R (B.obj i).obj 1 (by omega)) ≫
        postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1 := by
  rw [postnikovCommonRightDenStandardClass, Category.assoc, postnikovCommonRightDenClassIso_zero,
    ← Category.assoc, postnikovCellClassOver_map]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
