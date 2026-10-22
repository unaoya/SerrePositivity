module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerImageSquareLaws
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageClass
public import SerrePositivity.KST.LocalizingInvariants.CochainBiprodMapComposition

/-!
概要：元の可換正方形に沿う係数像の射は、源 class の実平方零正方形を与える。
方針：像射影との整合を直和の二射影へ送り、元の摂動 class の自然性と合成する。
規約：底変更・元の class を保持。使われ方：源側像拡大の実模型射。
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

def postnikovSourceImageSquareZeroMap :
    SquareZero.algebra (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1) ⟶
      SquareZero.algebra (postnikov R B' n) (postnikovShiftedLayerImage R f' n hn 1) :=
  SquareZero.mapOver (postnikovMap R s n) (postnikovShiftedLayerImage R f n hn 1)
    (postnikovShiftedLayerImage R f' n hn 1)
    (postnikovShiftedLayerImageSquareMap R n hn 1 f f' s t h)

lemma postnikovSourceImageCoefficientMap_square : postnikovSourceImageCoefficientMap R f n hn ≫
    postnikovSourceImageSquareZeroMap R n hn f f' s t h =
      postnikovDerivationTargetMap R s n hn ≫ postnikovSourceImageCoefficientMap R f' n hn := by
  let p : (postnikovShiftedLayerBimodule R B n hn 1).X ⟶
      (postnikovShiftedLayerImage R f n hn 1).X :=
    (postnikovShiftedLayerImageProjection R f n hn 1).hom
  let p' : (postnikovShiftedLayerBimodule R B' n hn 1).X ⟶
      (postnikovShiftedLayerImage R f' n hn 1).X :=
    (postnikovShiftedLayerImageProjection R f' n hn 1).hom
  let v : (postnikovShiftedLayerImage R f n hn 1).X ⟶
      (postnikovShiftedLayerImage R f' n hn 1).X :=
    (postnikovShiftedLayerImageSquareMap R n hn 1 f f' s t h).hom
  let u : (postnikovShiftedLayerBimodule R B n hn 1).X ⟶
      (postnikovShiftedLayerBimodule R B' n hn 1).X :=
    (postnikovShiftedLayerMap R B n hn 1 s).hom
  have hp : p ≫ v = u ≫ p' := postnikovShiftedLayerImageSquareMap_projection R n hn 1 f f' s t h
  apply Mon.Hom.ext
  change biprod.map (𝟙 (postnikov R B n).X) p ≫ biprod.map (postnikovMap R s n).hom v =
    biprod.map (postnikovMap R s n).hom u ≫ biprod.map (𝟙 (postnikov R B' n).X) p'
  rw [cochainBiprodMap_comp, cochainBiprodMap_comp, Category.id_comp, Category.comp_id, hp]

lemma postnikovSourceImageClass_square : postnikovPerturbedMap R s n hn ≫
    postnikovSourceImageClass R f' n hn =
      postnikovSourceImageClass R f n hn ≫ postnikovSourceImageSquareZeroMap R n hn f f' s t h := by
  change postnikovPerturbedMap R s n hn ≫
    (postnikovPerturbedClass R B' n hn ≫ postnikovSourceImageCoefficientMap R f' n hn) =
      (postnikovPerturbedClass R B n hn ≫ postnikovSourceImageCoefficientMap R f n hn) ≫
        postnikovSourceImageSquareZeroMap R n hn f f' s t h
  calc
    _ = (postnikovPerturbedMap R s n hn ≫ postnikovPerturbedClass R B' n hn) ≫
        postnikovSourceImageCoefficientMap R f' n hn := (Category.assoc _ _ _).symm
    _ = (postnikovPerturbedClass R B n hn ≫ postnikovDerivationTargetMap R s n hn) ≫
        postnikovSourceImageCoefficientMap R f' n hn :=
      congrArg (fun z => z ≫ postnikovSourceImageCoefficientMap R f' n hn)
        (postnikovPerturbedClass_naturality R s n hn)
    _ = postnikovPerturbedClass R B n hn ≫
        (postnikovSourceImageCoefficientMap R f n hn ≫
          postnikovSourceImageSquareZeroMap R n hn f f' s t h) :=
      (Category.assoc _ _ _).trans (congrArg (fun z => postnikovPerturbedClass R B n hn ≫ z)
        (postnikovSourceImageCoefficientMap_square R n hn f f' s t h).symm)
    _ = _ := (Category.assoc _ _ _).symm

lemma postnikovSourceImageSquareZeroMap_zeroSection :
    postnikovMap R s n ≫
      SquareZero.zeroSection (postnikov R B' n) (postnikovShiftedLayerImage R f' n hn 1) =
        SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1) ≫
          postnikovSourceImageSquareZeroMap R n hn f f' s t h :=
  (SquareZero.zeroSection_mapOver _ _ _ _).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
