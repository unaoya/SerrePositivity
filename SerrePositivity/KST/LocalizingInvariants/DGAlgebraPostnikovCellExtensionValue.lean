module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPathCone
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageFactorisation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassConnective
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeConeEquiv

/-!
概要：元の隣接 Postnikov 拡大と cell class の模型を、connective 準同型反転後に比較する。
方針：既存の準同型 span を反転し、同じ二脚と全 class 経路の可換式を輸送する。
規約：通常圏の実同型であり、一般の導来写像空間の普遍性とは区別する。
使われ方：平方零微分摂動の拡大を、底を保つ cell class の零化表示へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open HomotopyPullbackModel
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

abbrev postnikovCellExtensionModel := algebra R (postnikovCellClass R B n hn)
  (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))

lemma postnikovCellExtensionModel_isConnective :
    IsConnective R (postnikovCellExtensionModel R B n hn) :=
  (quasiIso_isConnective_iff R (postnikovCellHomotopyPullbackComparison R B n hn)
    (postnikovCellHomotopyPullbackComparison_quasiIso R B n hn)).2
      (postnikovClassModel_isConnective R B n hn)

variable {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)
  (hL : InvertsConnectiveQuasiIsos R L)
include hL

lemma postnikovUpperComparison_value_isIso :
    IsIso (L.map (postnikovHomotopyPullbackComparison R B n hn)) :=
  hL (postnikov_isConnective R B (n + 1)) (postnikovClassModel_isConnective R B n hn) _
    (postnikovHomotopyPullbackComparison_quasiIso R B n hn)

lemma postnikovCellComparison_value_isIso :
    IsIso (L.map (postnikovCellHomotopyPullbackComparison R B n hn)) :=
  hL (postnikovCellExtensionModel_isConnective R B n hn)
    (postnikovClassModel_isConnective R B n hn) _
      (postnikovCellHomotopyPullbackComparison_quasiIso R B n hn)

def postnikovCellExtensionValueIso :
    L.obj (postnikov R B (n + 1)) ≅ L.obj (postnikovCellExtensionModel R B n hn) := by
  have := postnikovUpperComparison_value_isIso R B n hn L hL
  have := postnikovCellComparison_value_isIso R B n hn L hL
  exact asIso (L.map (postnikovHomotopyPullbackComparison R B n hn)) ≪≫
    (asIso (L.map (postnikovCellHomotopyPullbackComparison R B n hn))).symm

lemma postnikovCellExtensionValueIso_comparison :
    (postnikovCellExtensionValueIso R B n hn L hL).hom ≫
      L.map (postnikovCellHomotopyPullbackComparison R B n hn) =
        L.map (postnikovHomotopyPullbackComparison R B n hn) := by
  have := postnikovCellComparison_value_isIso R B n hn L hL
  simp only [postnikovCellExtensionValueIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

lemma postnikovCellExtensionValueIso_right :
    (postnikovCellExtensionValueIso R B n hn L hL).hom ≫ L.map (right R
      (postnikovCellClass R B n hn) _) =
        L.map (postnikovTransition R B (n + 1) n (by omega)) := by
  rw [← postnikovCellHomotopyPullbackComparison_right R B n hn, L.map_comp,
    ← Category.assoc, postnikovCellExtensionValueIso_comparison, ← L.map_comp,
    postnikovHomotopyPullbackComparison_right]

lemma postnikovCellExtensionValueIso_left :
    (postnikovCellExtensionValueIso R B n hn L hL).hom ≫ L.map (left R
      (postnikovCellClass R B n hn) _ ≫ postnikovCellLift R B n hn) =
        L.map (postnikovPerturbedInclusion R B n hn) := by
  rw [← postnikovCellHomotopyPullbackComparison_left R B n hn, L.map_comp,
    ← Category.assoc, postnikovCellExtensionValueIso_comparison, ← L.map_comp,
    postnikovHomotopyPullbackComparison_left]

lemma postnikovCellExtensionValueIso_path :
    (postnikovCellExtensionValueIso R B n hn L hL).hom ≫ L.map (path R
      (postnikovCellClass R B n hn) _) =
        L.map (postnikovPerturbedInclusion R B n hn ≫ postnikovPerturbedClass R B n hn ≫
          Path.diagonal R (postnikovDerivationTarget R B n hn)) := by
  rw [← postnikovCellHomotopyPullbackComparison_path R B n hn, L.map_comp,
    ← Category.assoc, postnikovCellExtensionValueIso_comparison, ← L.map_comp,
    postnikovHomotopyPullbackComparison_path]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
