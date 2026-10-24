module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroTarget
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

lemma postnikovCommonRightClassIso_matrix : (postnikovCommonRightClassIso R hn f c d).hom.hom =
    biprod.map (𝟙 (postnikovCommonClassBase R hn f c d).X)
      (𝟙 ((postnikovLayer R (B.obj i).obj n)⟦(1 : ℤ)⟧)) := by
  change biprod.map (𝟙 (postnikovCommonClassBase R hn f c d).X)
    (postnikovCommonRightShiftedBaseIso R hn f c d 1).hom.hom = _
  rw [postnikovCommonRightShiftedBaseIso_hom]
  rfl

lemma postnikovCommonRightDenClassIso_matrix : (postnikovCommonRightDenClassIso R hn f c d).hom.hom =
    biprod.map (𝟙 (postnikovCommonClassBase R hn f c d).X)
      (𝟙 ((postnikovLayer R (B.obj i).obj n)⟦(1 : ℤ)⟧)) := by
  change biprod.map (𝟙 (postnikovCommonClassBase R hn f c d).X)
    (postnikovCommonRightShiftedDenBaseIso R hn f c d 1).hom.hom = _
  rw [postnikovCommonRightShiftedDenBaseIso_hom]
  rfl

lemma postnikovCommonRightClassIso_zero : (postnikovCommonRightClassIso R hn f c d).hom ≫
    postnikovCommonRightClassToZero R hn f c d =
      SquareZero.baseChangeMap (postnikovCommonRightBase R hn f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj n hn 1) ≫
      postnikovClassToZeroBase R (B.obj i).obj n hn 1 := by
  apply Mon.Hom.ext
  change (postnikovCommonRightClassIso R hn f c d).hom.hom ≫
    (postnikovCommonRightClassToZero R hn f c d).hom =
      (SquareZero.baseChangeMap (postnikovCommonRightBase R hn f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj n hn 1)).hom ≫
      (postnikovClassToZeroBase R (B.obj i).obj n hn 1).hom
  rw [postnikovCommonRightClassIso_matrix, postnikovCommonRightClassToZero_hom,
    SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom,
    congrArg Mon.Hom.hom (postnikovCommonRightZeroBase_num R hn f c d)]
  change biprod.map (𝟙 (postnikovCommonClassBase R hn f c d).X) (𝟙 _) ≫
      biprod.map ((postnikovCommonRightBase R hn f c d).hom ≫
        (postnikovTransition R (B.obj i).obj n 0 (by omega)).hom) (𝟙 _) =
    biprod.map (postnikovCommonRightBase R hn f c d).hom (𝟙 _) ≫
      biprod.map (postnikovTransition R (B.obj i).obj n 0 (by omega)).hom (𝟙 _)
  apply biprod.hom_ext <;> simp [Category.assoc]

lemma postnikovCommonRightDenClassIso_zero : (postnikovCommonRightDenClassIso R hn f c d).hom ≫
    postnikovCommonRightClassToZero R hn f c d =
      SquareZero.baseChangeMap (postnikovCommonRightDenBase R hn f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj n hn 1) ≫
      postnikovClassToZeroBase R (B.obj i).obj n hn 1 := by
  apply Mon.Hom.ext
  change (postnikovCommonRightDenClassIso R hn f c d).hom.hom ≫
    (postnikovCommonRightClassToZero R hn f c d).hom =
      (SquareZero.baseChangeMap (postnikovCommonRightDenBase R hn f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj n hn 1)).hom ≫
      (postnikovClassToZeroBase R (B.obj i).obj n hn 1).hom
  rw [postnikovCommonRightDenClassIso_matrix, postnikovCommonRightClassToZero_hom,
    SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom,
    congrArg Mon.Hom.hom (postnikovCommonRightZeroBase_den R hn f c d)]
  change biprod.map (𝟙 (postnikovCommonClassBase R hn f c d).X) (𝟙 _) ≫
      biprod.map ((postnikovCommonRightDenBase R hn f c d).hom ≫
        (postnikovTransition R (B.obj i).obj n 0 (by omega)).hom) (𝟙 _) =
    biprod.map (postnikovCommonRightDenBase R hn f c d).hom (𝟙 _) ≫
      biprod.map (postnikovTransition R (B.obj i).obj n 0 (by omega)).hom (𝟙 _)
  apply biprod.hom_ext <;> simp [Category.assoc]

lemma postnikovCommonRightStandardClass_zero : postnikovCommonRightStandardClass R hn f c d ≫
    postnikovCommonRightClassToZero R hn f c d =
    (cellResolutionMap R (postnikovCommonRightBase R hn f c d) ≫
      postnikovCellClass R (B.obj i).obj n hn) ≫
        postnikovClassToZeroBase R (B.obj i).obj n hn 1 := by
  rw [postnikovCommonRightStandardClass, Category.assoc, postnikovCommonRightClassIso_zero,
    ← Category.assoc, postnikovCellClassOver_map]

lemma postnikovCommonRightDenStandardClass_zero : postnikovCommonRightDenStandardClass R hn f c d ≫
    postnikovCommonRightClassToZero R hn f c d =
    (cellResolutionMap R (postnikovCommonRightDenBase R hn f c d) ≫
      postnikovCellClass R (B.obj i).obj n hn) ≫
        postnikovClassToZeroBase R (B.obj i).obj n hn 1 := by
  rw [postnikovCommonRightDenStandardClass, Category.assoc, postnikovCommonRightDenClassIso_zero,
    ← Category.assoc, postnikovCellClassOver_map]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
