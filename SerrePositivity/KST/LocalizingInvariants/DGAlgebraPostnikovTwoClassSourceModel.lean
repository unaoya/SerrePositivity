module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassModelMaps
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellHomotopyPullback
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeQuasiIso

/-!
概要：二切断逆の共通底の源拡大模型を、元の B の class 模型へ実準同型で比較する。
方針：元の分母と cell 比較の三つの準同型を使い、既存の摂動 class 比較へ接続する。
規約：元の右脚と底の分母を保持。使われ方：元の二切断代数を分母に取る実 roof。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def sourceCellMap : d.classSource R ⟶
    cellResolution R (postnikov R (B.obj d.layerInverse.zero.stage).obj 1) :=
  postnikovCommonClassCompatibilityToCell R f d.baseInverse d.layerInverse ≫
    cellResolutionMap R (d.lowerBaseInverse R).roof.denominator

lemma sourceCellMap_quasiIso : QuasiIso (d.sourceCellMap R).hom := by
  let α := postnikovCommonClassCompatibilityToCell R f d.baseInverse d.layerInverse
  have hα : QuasiIso α.hom := by
    have : QuasiIso (cellAugmentation R (d.classBase R)).hom := cellAugmentation_quasiIso R _
    have : QuasiIso (α.hom ≫ (cellAugmentation R (d.classBase R)).hom) := by
      change QuasiIso ((α ≫ cellAugmentation R (d.classBase R)).hom)
      rw [postnikovCommonClassCompatibilityToCell_projection]
      exact d.classProjection_quasiIso R
    exact quasiIso_of_comp_right α.hom (cellAugmentation R (d.classBase R)).hom
  exact quasiIso_comp _ _ (hφ := hα)
    (hφ' := cellResolutionMap_quasiIso R (d.lowerBaseInverse R).roof.denominator
      (d.lowerBaseInverse R).roof.denominator_quasiIso)

abbrev sourceCellModel : Mon (Complex R) := HomotopyPullbackModel.algebra R
  (postnikovCellClass R (B.obj d.layerInverse.zero.stage).obj 1 (by omega))
  (SquareZero.zeroSection (postnikov R (B.obj d.layerInverse.zero.stage).obj 1)
    (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) 1))

abbrev originalSourceModel : Mon (Complex R) := HomotopyPullbackModel.algebra R
  (postnikovPerturbedClass R (B.obj d.layerInverse.zero.stage).obj 1 (by omega))
  (SquareZero.zeroSection (postnikov R (B.obj d.layerInverse.zero.stage).obj 1)
    (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) 1))

def sourceToCellModel : d.sourceModel R ⟶ d.sourceCellModel R :=
  HomotopyPullbackModel.map R (d.sourceClass R) _
    (postnikovCellClass R (B.obj d.layerInverse.zero.stage).obj 1 (by omega)) _
    (d.sourceCellMap R)
    (SquareZero.baseChangeMap (d.lowerBaseInverse R).roof.denominator
      (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) 1))
    (d.lowerBaseInverse R).roof.denominator
    (by
      rw [sourceClass, Category.assoc, postnikovCellClassOver_map]
      exact (Category.assoc _ _ _).symm)
    (by exact (SquareZero.zeroSection_mapOver _ _ _ _).symm)

lemma sourceToCellModel_quasiIso : QuasiIso (d.sourceToCellModel R).hom :=
  HomotopyPullbackModel.map_quasiIso R _ _ _ _ _ _ _ _ _ (d.sourceCellMap_quasiIso R)
    (SquareZero.baseChangeMap_quasiIso _ _ (d.lowerBaseInverse R).roof.denominator_quasiIso)
    (d.lowerBaseInverse R).roof.denominator_quasiIso

def sourceToOriginalModel : d.sourceModel R ⟶ d.originalSourceModel R :=
  d.sourceToCellModel R ≫
    postnikovCellHomotopyPullbackComparison R (B.obj d.layerInverse.zero.stage).obj 1 (by omega)

lemma sourceToOriginalModel_quasiIso : QuasiIso (d.sourceToOriginalModel R).hom :=
  quasiIso_comp _ _ (hφ := d.sourceToCellModel_quasiIso R)
    (hφ' := postnikovCellHomotopyPullbackComparison_quasiIso R
      (B.obj d.layerInverse.zero.stage).obj 1 (by omega))

lemma sourceToOriginalModel_right : d.sourceToOriginalModel R ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ ≫
      (d.lowerBaseInverse R).roof.denominator := by
  rw [sourceToOriginalModel, Category.assoc, postnikovCellHomotopyPullbackComparison_right]
  exact HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
