module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassSourceModel

/-!
概要：共通底の標準 class 模型から、元の A の低い段の class 模型への実射を構成する。
方針：同じ分子と class の底変更式を cospan 射へ渡し、元の摂動比較へ接続する。
規約：標的比較の準同型性は仮定しない。使われ方：元の二切断への分子の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def targetBase : d.classBase R ⟶ postnikov R (A.obj j).obj 1 :=
  postnikovCommonClassRetractBase R f d.baseInverse d.layerInverse (hj := d.target_le)

def targetCellMap : d.classSource R ⟶ cellResolution R (postnikov R (A.obj j).obj 1) :=
  postnikovCommonClassCompatibilityToCell R f d.baseInverse d.layerInverse ≫
    cellResolutionMap R (d.targetBase R)

abbrev targetCellModel : Mon (Complex R) := HomotopyPullbackModel.algebra R
  (postnikovCellClass R (A.obj j).obj 1 (by omega))
  (SquareZero.zeroSection (postnikov R (A.obj j).obj 1)
    (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1))

abbrev originalTargetModel : Mon (Complex R) := HomotopyPullbackModel.algebra R
  (postnikovPerturbedClass R (A.obj j).obj 1 (by omega))
  (SquareZero.zeroSection (postnikov R (A.obj j).obj 1)
    (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1))

def targetToCellModel : d.targetModel R ⟶ targetCellModel (A := A) (j := j) R :=
  HomotopyPullbackModel.map R (d.targetClass R) _
    (postnikovCellClass R (A.obj j).obj 1 (by omega)) _ (d.targetCellMap R)
    (SquareZero.baseChangeMap (d.targetBase R)
      (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1))
    (d.targetBase R)
    (by
      let α := postnikovCommonClassCompatibilityToCell R f d.baseInverse d.layerInverse
      let a := d.targetBase R
      change (α ≫ cellResolutionMap R a) ≫
        postnikovCellClass R (A.obj j).obj 1 (by omega) =
          (α ≫ postnikovCellClassOver R (A.obj j).obj (d.classBase R) 1 (by omega) a) ≫
            SquareZero.baseChangeMap a
              (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1)
      rw [Category.assoc, Category.assoc, postnikovCellClassOver_map])
    (by exact (SquareZero.zeroSection_mapOver (d.targetBase R) (d.numeratorLayer R)
      (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1)
      (𝟙 (d.numeratorLayer R))).symm)

def targetToOriginalModel : d.targetModel R ⟶ originalTargetModel (A := A) (j := j) R :=
  d.targetToCellModel R ≫ postnikovCellHomotopyPullbackComparison R (A.obj j).obj 1 (by omega)

lemma targetToOriginalModel_right : d.targetToOriginalModel R ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ ≫
      (d.lowerBaseInverse R).roof.numerator := by
  rw [targetToOriginalModel, Category.assoc, postnikovCellHomotopyPullbackComparison_right]
  exact HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
