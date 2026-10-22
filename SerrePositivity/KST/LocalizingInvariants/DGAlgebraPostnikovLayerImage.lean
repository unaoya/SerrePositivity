module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayer
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImageSupport

/-!
概要：元の dg 代数射による shift Postnikov 層の像を、実双加群として供給する。
方針：底を源の切断に制限した既存の層射へ実像の構成を適用する。
規約：任意整数 shift、元の層射の因子分解を保持。使われ方：LT の像係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n) (s : ℤ)

def postnikovShiftedLayerImage : Bimod (postnikov R B n) (postnikov R B n) :=
  DGBimoduleImage.obj (postnikovShiftedLayerMap R B n hn s f)

def postnikovShiftedLayerImageInclusion : postnikovShiftedLayerImage R f n hn s ⟶
    bimoduleRestrict (postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn s) :=
  DGBimoduleImage.inclusion _

def postnikovShiftedLayerImageProjection : postnikovShiftedLayerBimodule R B n hn s ⟶
    postnikovShiftedLayerImage R f n hn s := DGBimoduleImage.projection _

lemma postnikovShiftedLayerImage_fac : postnikovShiftedLayerImageProjection R f n hn s ≫
    postnikovShiftedLayerImageInclusion R f n hn s = postnikovShiftedLayerMap R B n hn s f :=
  DGBimoduleImage.projection_inclusion _

lemma postnikovShiftedLayerImageInclusion_mono :
    Mono (postnikovShiftedLayerImageInclusion R f n hn s).hom :=
  DGBimoduleImage.inclusion_mono _

lemma postnikovShiftedLayerImageProjection_epi :
    Epi (postnikovShiftedLayerImageProjection R f n hn s).hom :=
  DGBimoduleImage.projection_epi _

lemma postnikovShiftedLayerImage_upperBound :
    (postnikovShiftedLayerImage R f n hn s).X.IsStrictlyLE (-(n + 1) - s) := by
  have : (bimoduleRestrict (postnikovMap R f n)
      (postnikovShiftedLayerBimodule R C n hn s)).X.IsStrictlyLE (-(n + 1) - s) :=
    postnikovShiftedLayer_upperBound R C n hn s
  exact DGBimoduleImage.upperBound _ _

lemma postnikovShiftedLayerImage_lowerBound :
    (postnikovShiftedLayerImage R f n hn s).X.IsStrictlyGE (-(n + 1) - s) := by
  have : (bimoduleRestrict (postnikovMap R f n)
      (postnikovShiftedLayerBimodule R C n hn s)).X.IsStrictlyGE (-(n + 1) - s) :=
    postnikovShiftedLayer_lowerBound R C n hn s
  exact DGBimoduleImage.lowerBound _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
