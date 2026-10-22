module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationSuccessor

/-!
概要：下段の比較が準同型なら、元の像因子分解の標的射は低次数で同型である。
方針：摂動底の射の準同型性を両射影で検出し、元の経路と模型比較を通じて移す。
規約：下段の準同型性を明示。使われ方：LT のレベル表示に必要な標的側の連結度。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovPerturbedMap_quasiIso (hf : QuasiIso (postnikovMap R f n).hom) :
    QuasiIso (postnikovPerturbedMap R f n hn).hom := by
  have := postnikovPerturbedProjection_quasiIso R C n hn
  have hc : QuasiIso ((postnikovPerturbedMap R f n hn).hom ≫
      (postnikovPerturbedProjection R C n hn).hom) := by
    have he : (postnikovPerturbedMap R f n hn).hom ≫
        (postnikovPerturbedProjection R C n hn).hom =
          (postnikovPerturbedProjection R B n hn).hom ≫ (postnikovMap R f n).hom :=
      congrArg Mon.Hom.hom (postnikovPerturbedProjection_naturality R f n hn)
    rw [he]
    exact quasiIso_comp _ _ (hφ := postnikovPerturbedProjection_quasiIso R B n hn) (hφ' := hf)
  exact quasiIso_of_comp_right (postnikovPerturbedMap R f n hn).hom
    (postnikovPerturbedProjection R C n hn).hom

lemma postnikovSourceImageToTarget_quasiIsoAt (hf : QuasiIso (postnikovMap R f n).hom)
    (j : ℤ) (hj : -n ≤ j) : QuasiIsoAt (postnikovSourceImageToTarget R f n hn).hom j := by
  let I := postnikovShiftedLayerImage R f n hn 1
  let N := postnikovShiftedLayerBimodule R C n hn 1
  have : I.X.IsStrictlyLE (-(n + 1) - 1) := postnikovShiftedLayerImage_upperBound R f n hn 1
  have : N.X.IsStrictlyLE (-(n + 1) - 1) := postnikovShiftedLayer_upperBound R C n hn 1
  have := SquareZeroExtension.projection_quasiIsoAt I (postnikovSourceImageClass R f n hn) j
    (I.X.isZero_of_isLE (-(n + 1) - 1) (j - 1) (by omega))
    (I.X.isZero_of_isLE (-(n + 1) - 1) j (by omega))
  have := SquareZeroExtension.projection_quasiIsoAt N (postnikovPerturbedClass R C n hn) j
    (N.X.isZero_of_isLE (-(n + 1) - 1) (j - 1) (by omega))
    (N.X.isZero_of_isLE (-(n + 1) - 1) j (by omega))
  have := postnikovPerturbedMap_quasiIso R f n hn hf
  let p := HomotopyPullbackModel.left R (postnikovPerturbedClass R C n hn)
    (SquareZero.zeroSection (postnikov R C n) N)
  have hc : QuasiIsoAt ((postnikovSourceImageToTarget R f n hn).hom ≫ p.hom) j := by
    have he : (postnikovSourceImageToTarget R f n hn).hom ≫ p.hom =
        (HomotopyPullbackModel.left R (postnikovSourceImageClass R f n hn)
          (SquareZero.zeroSection (postnikov R B n) I)).hom ≫
            (postnikovPerturbedMap R f n hn).hom :=
      congrArg Mon.Hom.hom (postnikovSourceImageToTarget_left R f n hn)
    rw [he]
    infer_instance
  exact quasiIsoAt_of_comp_right (postnikovSourceImageToTarget R f n hn).hom p.hom j

lemma postnikovImageFactorisationTarget_quasiIsoAt (hf : QuasiIso (postnikovMap R f n).hom)
    (j : ℤ) (hj : -n ≤ j) : QuasiIsoAt (postnikovImageFactorisationTarget R f n hn).hom j := by
  have := postnikovImageFactorisationComparison_quasiIso R f n hn
  have := postnikovSourceImageToTarget_quasiIsoAt R f n hn hf j hj
  have := postnikovHomotopyPullbackComparison_quasiIso R C n hn
  have hc : QuasiIsoAt ((postnikovImageFactorisationTarget R f n hn).hom ≫
      (postnikovHomotopyPullbackComparison R C n hn).hom) j := by
    apply ((HomotopyPullbackModel.witness R (postnikovSourceImageToTarget R f n hn)
      (postnikovHomotopyPullbackComparison R C n hn)).quasiIsoAt_iff j).mp
    change QuasiIsoAt ((postnikovImageFactorisationComparison R f n hn).hom ≫
      (postnikovSourceImageToTarget R f n hn).hom) j
    infer_instance
  exact quasiIsoAt_of_comp_right (postnikovImageFactorisationTarget R f n hn).hom
    (postnikovHomotopyPullbackComparison R C n hn).hom j

lemma postnikovImageFactorisationTarget_groups_bijective
    (hf : QuasiIso (postnikovMap R f n).hom) (j : ℤ) (hj : j ≤ n) :
    Function.Bijective ((groups R j).map (postnikovImageFactorisationTarget R f n hn)).hom :=
  (groups_map_bijective_iff R _ j).2
    (postnikovImageFactorisationTarget_quasiIsoAt R f n hn hf (-j) (by omega))

lemma postnikovImageFactorisationTarget_connected (hf : QuasiIso (postnikovMap R f n).hom) :
    IsConnected R (postnikovImageFactorisationTarget R f n hn) n :=
  ⟨fun j hj => (postnikovImageFactorisationTarget_groups_bijective R f n hn hf j hj.le).1,
    fun j hj => (postnikovImageFactorisationTarget_groups_bijective R f n hn hf j hj).2⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
