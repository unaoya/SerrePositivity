module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassModelMap

/-!
概要：源側像拡大から元の標的 class 模型への実射は、元の正方形に厳密に自然である。
方針：像包含の正方形を平方零代数射へ送り、模型の二脚と乗法的経路を照合する。
規約：元の toTarget 射を保持。使われ方：元の標的上段までの全因子分解の関手化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)
  (f : B ⟶ C) (f' : B' ⟶ C') (s : B ⟶ B') (t : C ⟶ C') (h : f ≫ t = s ≫ f')

include h in
lemma postnikovPerturbedMap_square : postnikovPerturbedMap R f n hn ≫
    postnikovPerturbedMap R t n hn = postnikovPerturbedMap R s n hn ≫
      postnikovPerturbedMap R f' n hn := by
  rw [← postnikovPerturbedMap_comp, h, postnikovPerturbedMap_comp]

lemma postnikovImageClassTargetMap_square : postnikovImageClassTargetMap R f n hn ≫
    postnikovDerivationTargetMap R t n hn = postnikovSourceImageSquareZeroMap R n hn f f' s t h ≫
      postnikovImageClassTargetMap R f' n hn := by
  let i : (postnikovShiftedLayerImage R f n hn 1).X ⟶
      (postnikovShiftedLayerBimodule R C n hn 1).X :=
    (postnikovShiftedLayerImageInclusion R f n hn 1).hom
  let i' : (postnikovShiftedLayerImage R f' n hn 1).X ⟶
      (postnikovShiftedLayerBimodule R C' n hn 1).X :=
    (postnikovShiftedLayerImageInclusion R f' n hn 1).hom
  let v : (postnikovShiftedLayerImage R f n hn 1).X ⟶
      (postnikovShiftedLayerImage R f' n hn 1).X :=
    (postnikovShiftedLayerImageSquareMap R n hn 1 f f' s t h).hom
  let u : (postnikovShiftedLayerBimodule R C n hn 1).X ⟶
      (postnikovShiftedLayerBimodule R C' n hn 1).X :=
    (postnikovShiftedLayerMap R C n hn 1 t).hom
  have hi : v ≫ i' = i ≫ u := postnikovShiftedLayerImageSquareMap_inclusion R n hn 1 f f' s t h
  have hb : (postnikovMap R f n).hom ≫ (postnikovMap R t n).hom =
      (postnikovMap R s n).hom ≫ (postnikovMap R f' n).hom :=
    congrArg Mon.Hom.hom (postnikovMap_square R n f f' s t h)
  apply Mon.Hom.ext
  change biprod.map (postnikovMap R f n).hom i ≫ biprod.map (postnikovMap R t n).hom u =
    biprod.map (postnikovMap R s n).hom v ≫ biprod.map (postnikovMap R f' n).hom i'
  rw [cochainBiprodMap_comp, cochainBiprodMap_comp, hb, hi]

lemma postnikovSourceImageToTarget_square : postnikovSourceImageToTarget R f n hn ≫
    postnikovClassModelMap R n hn t =
      postnikovSourceImageExtensionSquareMap R n hn f f' s t h ≫
        postnikovSourceImageToTarget R f' n hn := by
  apply HomotopyPullbackModel.hom_ext R (postnikovPerturbedClass R C' n hn)
    (SquareZero.zeroSection (postnikov R C' n) (postnikovShiftedLayerBimodule R C' n hn 1))
  · rw [Category.assoc, postnikovClassModelMap_left, ← Category.assoc,
      postnikovSourceImageToTarget_left,
      Category.assoc (postnikovSourceImageExtensionSquareMap R n hn f f' s t h),
      postnikovSourceImageToTarget_left,
      ← Category.assoc (postnikovSourceImageExtensionSquareMap R n hn f f' s t h),
      postnikovSourceImageExtensionSquareMap_left]
    simpa only [Category.assoc] using congrArg (fun z => HomotopyPullbackModel.left R
      (postnikovSourceImageClass R f n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1)) ≫ z)
      (postnikovPerturbedMap_square R n hn f f' s t h)
  · rw [Category.assoc, postnikovClassModelMap_right, ← Category.assoc,
      postnikovSourceImageToTarget_right,
      Category.assoc (postnikovSourceImageExtensionSquareMap R n hn f f' s t h),
      postnikovSourceImageToTarget_right,
      ← Category.assoc (postnikovSourceImageExtensionSquareMap R n hn f f' s t h),
      postnikovSourceImageExtensionSquareMap_right]
    simpa only [Category.assoc] using congrArg (fun z => HomotopyPullbackModel.right R
      (postnikovSourceImageClass R f n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1)) ≫ z)
      (postnikovMap_square R n f f' s t h)
  · rw [Category.assoc, postnikovClassModelMap_path, ← Category.assoc,
      postnikovSourceImageToTarget_path,
      Category.assoc (postnikovSourceImageExtensionSquareMap R n hn f f' s t h),
      postnikovSourceImageToTarget_path,
      ← Category.assoc (postnikovSourceImageExtensionSquareMap R n hn f f' s t h),
      postnikovSourceImageExtensionSquareMap_path]
    simp only [Category.assoc, ← Path.map_comp]
    rw [postnikovImageClassTargetMap_square R n hn f f' s t h]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
