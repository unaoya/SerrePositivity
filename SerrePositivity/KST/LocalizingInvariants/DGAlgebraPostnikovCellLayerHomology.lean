module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassLayerHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellHomotopyPullback
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionLayerMap

/-!
概要：cell class 模型の層を元の代数のホモロジーへ同定し、摂動模型への比較と照合する。
方針：cell augmentation による消滅の移送と、同じ係数の自然性を使う。
規約：元の比較射と符号を保持。使われ方：二切断候補の両端の層の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

lemma postnikovCellSource_homology_zero (z : ℤ) (hz : z < -n) :
    IsZero ((cellResolution R (postnikov R B n)).X.homology z) := by
  have := cellAugmentation_quasiIso R (postnikov R B n)
  have := postnikov_lowerBound R B n
  exact ((postnikov R B n).X.isZero_of_isGE (-n) z hz).of_iso
    (asIso (homologyMap (cellAugmentation R (postnikov R B n)).hom z))

def postnikovCellModelLayerHomologyIso :
    (HomotopyPullbackModel.algebra R (postnikovCellClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n)
        (postnikovShiftedLayerBimodule R B n hn 1))).X.homology (-(n + 1)) ≅
      B.X.homology (-(n + 1)) :=
  SquareZeroExtension.layerHomologyIso (postnikovShiftedLayerBimodule R B n hn 1)
    (postnikovCellClass R B n hn) (-(n + 1))
    (postnikovCellSource_homology_zero R B n _ (by omega))
    (postnikovCellSource_homology_zero R B n _ (by omega)) ≪≫
      postnikovShiftedLayerHomologyIso R B n hn 1

lemma postnikovCellComparison_layer :
    homologyMap (postnikovCellHomotopyPullbackComparison R B n hn).hom (-(n + 1)) ≫
      (postnikovClassModelLayerHomologyIso R B n hn).hom =
        (postnikovCellModelLayerHomologyIso R B n hn).hom := by
  let N := postnikovShiftedLayerBimodule R B n hn 1
  have hb : (𝟙 _ : SquareZero.algebra (postnikov R B n) N ⟶
      SquareZero.algebra (postnikov R B n) N).hom =
        biprod.map (𝟙 (postnikov R B n).X) (𝟙 N.X) := cochainBiprodMap_id.symm
  have h := SquareZeroExtension.layerHomologyIso_map_naturality N N
    (postnikovCellClass R B n hn) (postnikovPerturbedClass R B n hn)
    (postnikovCellLift R B n hn) (𝟙 (postnikov R B n)) (𝟙 _) (𝟙 N.X) hb
    (Category.comp_id _).symm (by simp) (-(n + 1))
    (postnikovCellSource_homology_zero R B n _ (by omega))
    (postnikovCellSource_homology_zero R B n _ (by omega))
    (postnikovPerturbedSource_homology_zero R n hn _ (by omega))
    (postnikovPerturbedSource_homology_zero R n hn _ (by omega))
  rw [postnikovCellHomotopyPullbackComparison, HomotopyPullbackModel.sourceMap_eq_map]
  simpa only [postnikovClassModelLayerHomologyIso, postnikovCellModelLayerHomologyIso,
    Iso.trans_hom, homologyMap_id, Category.comp_id, ← Category.assoc,
    postnikovCellClass, postnikovDerivationTarget, N] using
      congrArg (fun t => t ≫ (postnikovShiftedLayerHomologyIso R B n hn 1).hom) h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
