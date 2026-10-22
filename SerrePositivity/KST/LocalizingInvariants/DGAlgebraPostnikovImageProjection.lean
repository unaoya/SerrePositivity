module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageExtensionHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathQuasiIso

/-!
概要：像拡大の元の右射影は、下段を保ち (n+1)-connected である。
方針：実模型の乗法的経路を底射影へ送り、左射影と準同型な底の合成と比較する。
規約：元の右射影と整数次数群を使用。使われ方：像拡大の連結度と値の比較。
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

abbrev postnikovImageProjection : postnikovImageExtension R f n hn ⟶ postnikov R B n :=
  HomotopyPullbackModel.right R _ _

def postnikovImageProjectionWitness : Path.Witness R
    (HomotopyPullbackModel.left R _ _ ≫ postnikovImageBase R f n hn)
    (postnikovImageProjection R f n hn) := by
  have w := (HomotopyPullbackModel.witness R (postnikovImageClass R f n hn)
    (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1))).postcomp
      (SquareZero.projection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1))
  simpa only [postnikovImageBase, postnikovImageProjection, Category.assoc,
    SquareZero.zeroSection_projection, Category.comp_id] using w

lemma postnikovImageProjection_quasiIsoAt (j : ℤ) (hj : -n ≤ j) :
    QuasiIsoAt (postnikovImageProjection R f n hn).hom j := by
  have := postnikovImageExtensionProjection_quasiIsoAt R f n hn j hj
  have := postnikovImageBase_quasiIso R f n hn
  apply ((postnikovImageProjectionWitness R f n hn).quasiIsoAt_iff j).mp
  change QuasiIsoAt ((HomotopyPullbackModel.left R (postnikovImageClass R f n hn)
    (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1))).hom ≫
      (postnikovImageBase R f n hn).hom) j
  infer_instance

lemma postnikovImageProjection_groups_bijective (j : ℤ) (hj : j ≤ n) :
    Function.Bijective ((groups R j).map (postnikovImageProjection R f n hn)).hom :=
  (groups_map_bijective_iff R _ j).2
    (postnikovImageProjection_quasiIsoAt R f n hn (-j) (by omega))

lemma postnikovImageProjection_connected :
    IsConnected R (postnikovImageProjection R f n hn) (n + 1) := by
  refine ⟨fun j hj => (postnikovImageProjection_groups_bijective R f n hn j (by omega)).1, ?_⟩
  intro j hj
  by_cases h : j ≤ n
  · exact (postnikovImageProjection_groups_bijective R f n hn j h).2
  · have := postnikov_groups_subsingleton R B n j (by omega)
    exact Function.surjective_to_subsingleton _

lemma postnikovImageExtension_isConnective : IsConnective R (postnikovImageExtension R f n hn) := by
  apply (CochainComplex.isLE_iff _ 0).2
  intro j hj
  have := postnikovImageProjection_quasiIsoAt R f n hn j (by omega)
  exact (exactAt_iff_of_quasiIsoAt (postnikovImageProjection R f n hn).hom j).2
    (CochainComplex.exactAt_of_isLE (postnikov R B n).X 0 j hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
