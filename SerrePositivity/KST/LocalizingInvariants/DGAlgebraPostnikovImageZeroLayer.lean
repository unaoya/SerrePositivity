module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageHomology
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationConnectivity
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionProjection

/-!
概要：元の新しい層のホモロジー射が零なら、実像因子分解の中間代数は源の下段へ準同型。
方針：実係数像の集中次数と像同型で全ホモロジーを消し、元の平方零拡大射影を計算する。
規約：実準同型と元の源三角形を保持。使われ方：pro 零遷移を実切断の比較へ持ち上げる。
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

lemma postnikovShiftedLayerImage_homology_zero_of_zero (s j : ℤ)
    (h : homologyMap f.hom (-(n + 1)) = 0) :
    IsZero ((postnikovShiftedLayerImage R f n hn s).X.homology j) := by
  let c : ℤ := -(n + 1) - s
  have : (postnikovShiftedLayerImage R f n hn s).X.IsStrictlyLE c :=
    postnikovShiftedLayerImage_upperBound R f n hn s
  have : (postnikovShiftedLayerImage R f n hn s).X.IsStrictlyGE c :=
    postnikovShiftedLayerImage_lowerBound R f n hn s
  by_cases he : j = c
  · subst j
    have hz : IsZero (image (homologyMap f.hom (-(n + 1)))) := by
      apply IsZero.of_epi_eq_zero (factorThruImage (homologyMap f.hom (-(n + 1))))
      apply (cancel_mono (image.ι (homologyMap f.hom (-(n + 1))))).1
      rw [image.fac, zero_comp]
      exact h
    exact hz.of_iso (postnikovShiftedLayerImageHomologyIso R f n hn s)
  · by_cases hj : j < c
    · exact (postnikovShiftedLayerImage R f n hn s).X.isZero_of_isGE c j hj
    · exact (postnikovShiftedLayerImage R f n hn s).X.isZero_of_isLE c j (by omega)

lemma postnikovSourceImageProjection_quasiIso_of_zero
    (h : homologyMap f.hom (-(n + 1)) = 0) :
    QuasiIso (postnikovSourceImageProjection R f n hn).hom := by
  rw [quasiIso_iff]
  intro j
  exact SquareZeroExtension.right_quasiIsoAt _ _ (postnikovSourceImageBase_quasiIso R f n hn) j
    (postnikovShiftedLayerImage_homology_zero_of_zero R f n hn 1 (j - 1) h)
    (postnikovShiftedLayerImage_homology_zero_of_zero R f n hn 1 j h)

def postnikovImageFactorisationBaseProjection : postnikovImageFactorisationObject R f n hn ⟶
    postnikov R B n :=
  postnikovImageFactorisationComparison R f n hn ≫ postnikovSourceImageProjection R f n hn

lemma postnikovImageFactorisationBaseProjection_quasiIso_of_zero
    (h : homologyMap f.hom (-(n + 1)) = 0) :
    QuasiIso (postnikovImageFactorisationBaseProjection R f n hn).hom :=
  quasiIso_comp _ _ (hφ := postnikovImageFactorisationComparison_quasiIso R f n hn)
    (hφ' := postnikovSourceImageProjection_quasiIso_of_zero R f n hn h)

lemma postnikovImageFactorisationSource_base : postnikovImageFactorisationSource R f n hn ≫
    postnikovImageFactorisationBaseProjection R f n hn =
      postnikovTransition R B (n + 1) n (by omega) := by
  rw [postnikovImageFactorisationBaseProjection, ← Category.assoc,
    postnikovImageFactorisationSource_comparison]
  exact postnikovSourceImageFactor_right R f n hn

def postnikovImageFactorisationBaseWitness : Path.Witness R
    (postnikovImageFactorisationBaseProjection R f n hn ≫ postnikovMap R f n)
    (postnikovImageFactorisationTarget R f n hn ≫
      postnikovTransition R C (n + 1) n (by omega)) := by
  have w := (HomotopyPullbackModel.witness R (postnikovSourceImageToTarget R f n hn)
    (postnikovHomotopyPullbackComparison R C n hn)).postcomp
      (HomotopyPullbackModel.right R (postnikovPerturbedClass R C n hn)
        (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1)))
  simpa only [postnikovImageFactorisationBaseProjection, postnikovImageFactorisationComparison,
    postnikovSourceImageProjection, postnikovImageFactorisationTarget, Category.assoc,
    postnikovSourceImageToTarget_right, postnikovHomotopyPullbackComparison_right] using w

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
