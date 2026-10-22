module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageClassComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovHomotopyPullback

/-!
概要：源の実 Postnikov class を係数射影で送り、像への実 class を構成する。
方針：元の源 class を後合成し、係数像の epi-mono 分解と厳密な自然性を使う。
規約：源の摂動代数を保持。使われ方：源上段から像拡大への実因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

def postnikovSourceImageCoefficientMap := SquareZero.coefficientMap (postnikov R B n)
  (postnikovShiftedLayerImageProjection R f n hn 1)

lemma postnikovSourceImageCoefficientMap_zero :
    SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1) ≫
      postnikovSourceImageCoefficientMap R f n hn =
        SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1) := by
  apply Mon.Hom.ext
  change biprod.inl ≫ biprod.map (𝟙 _) _ = biprod.inl
  rw [biprod.inl_map, Category.id_comp]

lemma postnikovSourceImageCoefficientMap_fac : postnikovSourceImageCoefficientMap R f n hn ≫
    postnikovImageClassTargetMap R f n hn = postnikovDerivationTargetMap R f n hn := by
  apply Mon.Hom.ext
  change biprod.map (𝟙 _) (postnikovShiftedLayerImageProjection R f n hn 1).hom ≫
    biprod.map (postnikovMap R f n).hom (postnikovShiftedLayerImageInclusion R f n hn 1).hom =
      biprod.map (postnikovMap R f n).hom (postnikovShiftedLayerMap R B n hn 1 f).hom
  have hf : (postnikovShiftedLayerImageProjection R f n hn 1).hom ≫
      (postnikovShiftedLayerImageInclusion R f n hn 1).hom =
        (postnikovShiftedLayerMap R B n hn 1 f).hom :=
    congrArg Bimod.Hom.hom (postnikovShiftedLayerImage_fac R f n hn 1)
  apply biprod.hom_ext
  · simp [Category.assoc]
  · simp only [Category.assoc, biprod.map_snd]
    rw [← Category.assoc, biprod.map_snd, Category.assoc, hf]

def postnikovSourceImageClass : postnikovPerturbedExtension R B n hn ⟶
    SquareZero.algebra (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1) :=
  postnikovPerturbedClass R B n hn ≫ postnikovSourceImageCoefficientMap R f n hn

lemma postnikovSourceImageClass_projection : postnikovSourceImageClass R f n hn ≫
    SquareZero.projection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1) =
      postnikovPerturbedProjection R B n hn := by
  rw [postnikovSourceImageClass, Category.assoc, postnikovSourceImageCoefficientMap,
    SquareZero.coefficientMap_projection, postnikovPerturbedClass_projection]

lemma postnikovSourceImageClass_inclusion : postnikovSourceImageClass R f n hn ≫
    postnikovImageClassTargetMap R f n hn =
      postnikovPerturbedMap R f n hn ≫ postnikovPerturbedClass R C n hn := by
  rw [postnikovSourceImageClass, Category.assoc, postnikovSourceImageCoefficientMap_fac,
    postnikovPerturbedClass_naturality]

lemma postnikovPerturbedInclusion_sourceImageClass : postnikovPerturbedInclusion R B n hn ≫
    postnikovSourceImageClass R f n hn = postnikovTransition R B (n + 1) n (by omega) ≫
      SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1) := by
  rw [postnikovSourceImageClass, ← Category.assoc, postnikovPerturbedInclusion_class,
    Category.assoc, postnikovSourceImageCoefficientMap_zero]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
