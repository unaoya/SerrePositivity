module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellExtensionValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellAugmentation

/-!
概要：元の Postnikov 拡大を、底を固定した cell class の全経路付き零化模型と比較する。
方針：cell augmentation の次数全射性から相対比較の準同型性を導き、実 span を反転する。
規約：connective 準同型だけの反転で十分。一般の導来写像空間の普遍性は別に残す。
使われ方：同じ底への射影と class 経路を保つ Postnikov 拡大の表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

abbrev postnikovCellRelativeExtensionModel := SquareZeroExtension.relativeModel
  (postnikovShiftedLayerBimodule R B n hn 1) (postnikovCellClass R B n hn)

abbrev postnikovCellRelativeExtensionComparison : postnikovCellRelativeExtensionModel R B n hn ⟶
    postnikovCellExtensionModel R B n hn := SquareZeroExtension.relativeComparison _ _

lemma postnikovCellRelativeExtensionComparison_quasiIso :
    QuasiIso (postnikovCellRelativeExtensionComparison R B n hn).hom := by
  apply SquareZeroExtension.relativeComparison_quasiIso
  intro k
  rw [postnikovCellClass_projection]
  exact cellAugmentation_surjective R (postnikov R B n) k

lemma postnikovCellRelativeExtensionModel_isConnective :
    IsConnective R (postnikovCellRelativeExtensionModel R B n hn) :=
  (quasiIso_isConnective_iff R (postnikovCellRelativeExtensionComparison R B n hn)
    (postnikovCellRelativeExtensionComparison_quasiIso R B n hn)).2
      (postnikovCellExtensionModel_isConnective R B n hn)

def postnikovCellRelativePathConeEquiv (T : Mon (Complex R)) :
    (T ⟶ postnikovCellRelativeExtensionModel R B n hn) ≃
      SquareZeroExtension.RelativePathCone (postnikovShiftedLayerBimodule R B n hn 1)
        (postnikovCellClass R B n hn) T := SquareZeroExtension.relativeHomPathConeEquiv _ _ _

variable {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)
  (hL : InvertsConnectiveQuasiIsos R L)
include hL

lemma postnikovCellRelativeComparison_value_isIso :
    IsIso (L.map (postnikovCellRelativeExtensionComparison R B n hn)) :=
  hL (postnikovCellRelativeExtensionModel_isConnective R B n hn)
    (postnikovCellExtensionModel_isConnective R B n hn) _
      (postnikovCellRelativeExtensionComparison_quasiIso R B n hn)

def postnikovCellRelativeExtensionValueIso :
    L.obj (postnikov R B (n + 1)) ≅ L.obj (postnikovCellRelativeExtensionModel R B n hn) := by
  have := postnikovCellRelativeComparison_value_isIso R B n hn L hL
  exact postnikovCellExtensionValueIso R B n hn L hL ≪≫
    (asIso (L.map (postnikovCellRelativeExtensionComparison R B n hn))).symm

lemma postnikovCellRelativeExtensionValueIso_comparison :
    (postnikovCellRelativeExtensionValueIso R B n hn L hL).hom ≫
      L.map (postnikovCellRelativeExtensionComparison R B n hn) =
        (postnikovCellExtensionValueIso R B n hn L hL).hom := by
  have := postnikovCellRelativeComparison_value_isIso R B n hn L hL
  simp only [postnikovCellRelativeExtensionValueIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

lemma postnikovCellRelativeExtensionValueIso_right :
    (postnikovCellRelativeExtensionValueIso R B n hn L hL).hom ≫ L.map
      (SquareZeroExtension.relativeRight (postnikovShiftedLayerBimodule R B n hn 1)
        (postnikovCellClass R B n hn)) =
          L.map (postnikovTransition R B (n + 1) n (by omega)) := by
  rw [← SquareZeroExtension.relativeComparison_right, L.map_comp, ← Category.assoc]
  change ((postnikovCellRelativeExtensionValueIso R B n hn L hL).hom ≫
    L.map (postnikovCellRelativeExtensionComparison R B n hn)) ≫ _ = _
  rw [postnikovCellRelativeExtensionValueIso_comparison,
    postnikovCellExtensionValueIso_right]

lemma postnikovCellRelativeExtensionValueIso_left :
    (postnikovCellRelativeExtensionValueIso R B n hn L hL).hom ≫ L.map
      (SquareZeroExtension.relativeLeft (postnikovShiftedLayerBimodule R B n hn 1)
        (postnikovCellClass R B n hn) ≫ postnikovCellLift R B n hn) =
          L.map (postnikovPerturbedInclusion R B n hn) := by
  rw [← SquareZeroExtension.relativeComparison_left, Category.assoc, L.map_comp,
    ← Category.assoc]
  change ((postnikovCellRelativeExtensionValueIso R B n hn L hL).hom ≫
    L.map (postnikovCellRelativeExtensionComparison R B n hn)) ≫ _ = _
  rw [postnikovCellRelativeExtensionValueIso_comparison, postnikovCellExtensionValueIso_left]

lemma postnikovCellRelativeExtensionValueIso_path :
    (postnikovCellRelativeExtensionValueIso R B n hn L hL).hom ≫ L.map
      (SquareZeroExtension.relativePath (postnikovShiftedLayerBimodule R B n hn 1)
        (postnikovCellClass R B n hn)) =
          L.map (postnikovPerturbedInclusion R B n hn ≫ postnikovPerturbedClass R B n hn ≫
            Path.diagonal R (postnikovDerivationTarget R B n hn)) := by
  rw [← SquareZeroExtension.relativeComparison_path, L.map_comp, ← Category.assoc]
  change ((postnikovCellRelativeExtensionValueIso R B n hn L hL).hom ≫
    L.map (postnikovCellRelativeExtensionComparison R B n hn)) ≫ _ = _
  rw [postnikovCellRelativeExtensionValueIso_comparison, postnikovCellExtensionValueIso_path]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
