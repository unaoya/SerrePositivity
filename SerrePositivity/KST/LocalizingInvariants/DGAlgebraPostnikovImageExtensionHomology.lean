module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageExtension
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageHomology
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionHomology

/-!
概要：元の像拡大の新しい層は、元の代数射のホモロジー像と同型である。
方針：準同型な構成底で源の下端消滅を移し、実 cocone 短完全列と元の係数像比較を合成。
規約：元の実射影の次数別準同型性も保持。使われ方：LT の連結な因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

include f hn in
lemma postnikovImageSource_homology_zero (j : ℤ) (hj : j < -n) :
    IsZero ((postnikovImageClassSource R (B := B) n).X.homology j) := by
  have := postnikovImageBase_quasiIso R f n hn
  have : IsIso (homologyMap (postnikovImageBase R f n hn).hom j) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  exact ((postnikov R B n).X.isZero_of_isGE (-n) j hj).of_iso
    (asIso (homologyMap (postnikovImageBase R f n hn).hom j))

def postnikovImageExtensionLayerHomologyIso :
    (postnikovImageExtension R f n hn).X.homology (-(n + 1)) ≅
      image (homologyMap f.hom (-(n + 1))) :=
  SquareZeroExtension.layerHomologyIso (postnikovShiftedLayerImage R f n hn 1)
    (postnikovImageClass R f n hn) (-(n + 1))
    (postnikovImageSource_homology_zero R f n hn _ (by omega))
    (postnikovImageSource_homology_zero R f n hn _ (by omega)) ≪≫
      postnikovShiftedLayerImageHomologyIso R f n hn 1

lemma postnikovImageExtensionProjection_quasiIsoAt (j : ℤ) (hj : -n ≤ j) :
    QuasiIsoAt (HomotopyPullbackModel.left R (postnikovImageClass R f n hn)
      (SquareZero.zeroSection (postnikov R B n)
        (postnikovShiftedLayerImage R f n hn 1))).hom j := by
  have : (postnikovShiftedLayerImage R f n hn 1).X.IsStrictlyLE (-(n + 1) - 1) :=
    postnikovShiftedLayerImage_upperBound R f n hn 1
  exact SquareZeroExtension.projection_quasiIsoAt _ _ j
    ((postnikovShiftedLayerImage R f n hn 1).X.isZero_of_isLE (-(n + 1) - 1) (j - 1) (by omega))
    ((postnikovShiftedLayerImage R f n hn 1).X.isZero_of_isLE (-(n + 1) - 1) j (by omega))

lemma postnikovImageExtension_homology_zero (j : ℤ) (hj : j < -(n + 1)) :
    IsZero ((postnikovImageExtension R f n hn).X.homology j) := by
  have : (postnikovShiftedLayerImage R f n hn 1).X.IsStrictlyGE (-(n + 1) - 1) :=
    postnikovShiftedLayerImage_lowerBound R f n hn 1
  exact SquareZeroExtension.model_homology_isZero _ _ j
    ((postnikovShiftedLayerImage R f n hn 1).X.isZero_of_isGE (-(n + 1) - 1) (j - 1) (by omega))
    (postnikovImageSource_homology_zero R f n hn j (by omega))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
