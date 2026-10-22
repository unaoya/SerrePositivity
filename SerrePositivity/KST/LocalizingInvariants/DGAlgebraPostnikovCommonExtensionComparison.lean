module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageExtensionComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellHomotopyPullback

/-!
概要：共通底の拡大模型から、元の標的 cell class と隣接拡大の比較へ接続する。
方針：元の二重 cell 源の比較を使い、下段の準同型性から実模型射の準同型性を得る。
規約：右脚を厳密に保持。元の上段との比較には既存の準同型 span を再利用する。
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

def postnikovCommonCellSource : cellResolution R (cellResolution R (postnikov R B n)) ⟶
    cellResolution R (postnikov R C n) :=
  cellAugmentation R (cellResolution R (postnikov R B n)) ≫ cellResolutionMap R (postnikovMap R f n)

lemma postnikovCommonCellSource_quasiIso (hf : QuasiIso (postnikovMap R f n).hom) :
    QuasiIso (postnikovCommonCellSource R f n).hom :=
  quasiIso_comp _ _ (hφ := cellAugmentation_quasiIso R _)
    (hφ' := cellResolutionMap_quasiIso R _ hf)

abbrev postnikovCellClassExtension := HomotopyPullbackModel.algebra R (postnikovCellClass R C n hn)
  (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1))

def postnikovCommonExtensionToCell : postnikovCommonExtension R f n hn ⟶
    postnikovCellClassExtension R (C := C) n hn :=
  HomotopyPullbackModel.map R _ _ _ _ (postnikovCommonCellSource R f n) (𝟙 _) (𝟙 _)
    (by rw [postnikovCommonCellSource, classCommonTarget, Category.assoc, Category.comp_id])
    (by simp)

lemma postnikovCommonExtensionToCell_quasiIso (hf : QuasiIso (postnikovMap R f n).hom) :
    QuasiIso (postnikovCommonExtensionToCell R f n hn).hom :=
  HomotopyPullbackModel.map_quasiIso R _ _ _ _ _ _ _ _ _
    (postnikovCommonCellSource_quasiIso R f n hf) (quasiIso_of_isIso _) (quasiIso_of_isIso _)

lemma postnikovCommonExtensionToCell_right : postnikovCommonExtensionToCell R f n hn ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ :=
  (HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

def postnikovCellExtensionToPerturbed : postnikovCellClassExtension R (C := C) n hn ⟶
    HomotopyPullbackModel.algebra R (postnikovPerturbedClass R C n hn)
      (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1)) :=
  postnikovCellHomotopyPullbackComparison R C n hn

lemma postnikovCellExtensionToPerturbed_quasiIso :
    QuasiIso (postnikovCellExtensionToPerturbed R (C := C) n hn).hom :=
  postnikovCellHomotopyPullbackComparison_quasiIso R C n hn

lemma postnikovCellExtensionToPerturbed_right : postnikovCellExtensionToPerturbed R (C := C) n hn ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ :=
  postnikovCellHomotopyPullbackComparison_right R C n hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
