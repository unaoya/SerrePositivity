module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageFactorisation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageHomology
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionProjection

/-!
概要：源 class の像拡大の新しい層と、元の源上段からの連結な因子射を計算する。
方針：準同型な摂動底と係数像を実拡大のホモロジー計算へ渡し、元の遷移射を消去する。
規約：像拡大への源射は構成済みの実代数射。使われ方：LT の連結なレベル表示。
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

lemma postnikovSourceImageBase_quasiIso : QuasiIso (postnikovSourceImageClass R f n hn ≫
    SquareZero.projection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1)).hom := by
  rw [postnikovSourceImageClass_projection]
  exact postnikovPerturbedProjection_quasiIso R B n hn

lemma postnikovPerturbedSource_homology_zero (j : ℤ) (hj : j < -n) :
    IsZero ((postnikovPerturbedExtension R B n hn).X.homology j) := by
  have := postnikovPerturbedProjection_quasiIso R B n hn
  exact ((postnikov R B n).X.isZero_of_isGE (-n) j hj).of_iso
    (asIso (homologyMap (postnikovPerturbedProjection R B n hn).hom j))

def postnikovSourceImageLayerHomologyIso :
    (postnikovSourceImageExtension R f n hn).X.homology (-(n + 1)) ≅
      image (homologyMap f.hom (-(n + 1))) :=
  SquareZeroExtension.layerHomologyIso (postnikovShiftedLayerImage R f n hn 1)
    (postnikovSourceImageClass R f n hn) (-(n + 1))
    (postnikovPerturbedSource_homology_zero R n hn _ (by omega))
    (postnikovPerturbedSource_homology_zero R n hn _ (by omega)) ≪≫
      postnikovShiftedLayerImageHomologyIso R f n hn 1

abbrev postnikovSourceImageProjection : postnikovSourceImageExtension R f n hn ⟶
    postnikov R B n := HomotopyPullbackModel.right R _ _

lemma postnikovSourceImageProjection_quasiIsoAt (j : ℤ) (hj : -n ≤ j) :
    QuasiIsoAt (postnikovSourceImageProjection R f n hn).hom j := by
  have : (postnikovShiftedLayerImage R f n hn 1).X.IsStrictlyLE (-(n + 1) - 1) :=
    postnikovShiftedLayerImage_upperBound R f n hn 1
  exact SquareZeroExtension.right_quasiIsoAt _ _ (postnikovSourceImageBase_quasiIso R f n hn) j
    ((postnikovShiftedLayerImage R f n hn 1).X.isZero_of_isLE (-(n + 1) - 1) (j - 1) (by omega))
    ((postnikovShiftedLayerImage R f n hn 1).X.isZero_of_isLE (-(n + 1) - 1) j (by omega))

lemma postnikovSourceImageFactor_quasiIsoAt (j : ℤ) (hj : -n ≤ j) :
    QuasiIsoAt (postnikovSourceImageFactor R f n hn).hom j := by
  have := postnikovSourceImageProjection_quasiIsoAt R f n hn j hj
  have hc : QuasiIsoAt ((postnikovSourceImageFactor R f n hn).hom ≫
      (postnikovSourceImageProjection R f n hn).hom) j := by
    have he : (postnikovSourceImageFactor R f n hn).hom ≫
        (postnikovSourceImageProjection R f n hn).hom =
          (postnikovTransition R B (n + 1) n (by omega)).hom :=
      congrArg Mon.Hom.hom (postnikovSourceImageFactor_right R f n hn)
    rw [he]
    exact postnikovTransition_quasiIsoAt R B (n + 1) n (by omega) j hj
  exact quasiIsoAt_of_comp_right (postnikovSourceImageFactor R f n hn).hom
    (postnikovSourceImageProjection R f n hn).hom j

lemma postnikovSourceImageFactor_groups_bijective (j : ℤ) (hj : j ≤ n) :
    Function.Bijective ((groups R j).map (postnikovSourceImageFactor R f n hn)).hom :=
  (groups_map_bijective_iff R _ j).2
    (postnikovSourceImageFactor_quasiIsoAt R f n hn (-j) (by omega))

lemma postnikovSourceImageFactor_connected :
    IsConnected R (postnikovSourceImageFactor R f n hn) n :=
  ⟨fun j hj => (postnikovSourceImageFactor_groups_bijective R f n hn j hj.le).1,
    fun j hj => (postnikovSourceImageFactor_groups_bijective R f n hn j hj).2⟩

lemma postnikovSourceImageExtension_isConnective :
    IsConnective R (postnikovSourceImageExtension R f n hn) := by
  apply (CochainComplex.isLE_iff _ 0).2
  intro j hj
  have := postnikovSourceImageProjection_quasiIsoAt R f n hn j (by omega)
  exact (exactAt_iff_of_quasiIsoAt (postnikovSourceImageProjection R f n hn).hom j).2
    (CochainComplex.exactAt_of_isLE (postnikov R B n).X 0 j hj)

lemma postnikovSourceImageExtension_homology_zero (j : ℤ) (hj : j < -(n + 1)) :
    IsZero ((postnikovSourceImageExtension R f n hn).X.homology j) := by
  have : (postnikovShiftedLayerImage R f n hn 1).X.IsStrictlyGE (-(n + 1) - 1) :=
    postnikovShiftedLayerImage_lowerBound R f n hn 1
  exact SquareZeroExtension.model_homology_isZero _ _ j
    ((postnikovShiftedLayerImage R f n hn 1).X.isZero_of_isGE (-(n + 1) - 1) (j - 1) (by omega))
    (postnikovPerturbedSource_homology_zero R n hn j (by omega))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
