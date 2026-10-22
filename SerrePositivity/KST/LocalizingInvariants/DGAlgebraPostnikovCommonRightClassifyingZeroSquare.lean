module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroPath

/-!
概要：元の classifying 正方形を零底へ送り、全二重底射影を定数にする。
方針：元の指定右経路の零切断への射影を、非正次数源と零切断の次数境界で同定する。
規約：四隅だけでなく全底経路を保持。使われ方：相対輪郭補正への実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

local instance zeroSquare_apex_nonpositive :
    (postnikovCommonClassBase R f c d).X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof_nonpositive
local instance zeroSquare_target_lowerBound :
    (postnikov R (B.obj j).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj j).obj 0

/-- 元の cell 細分と右辺から得る同じ零底への射。 -/
def postnikovCommonRightClassifyingZeroProjection :
    cellResolution R (postnikovCommonRightCellSource R f c d) ⟶
      postnikov R (B.obj j).obj 0 :=
  cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
    postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightBase R f c d ≫
      postnikovMap R (B.transition hj).hom 1 ≫
        postnikovTransition R (B.obj j).obj 1 0 (by omega)

def postnikovCommonRightClassifyingZeroSquare : Path.Witness R
    ((cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedCellClassWitness R f c d).hom ≫
        Path.map R (postnikovDerivationTargetMap R (B.transition hj).hom 1 (by omega))) ≫
          Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1))
    ((cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedMappedClassWitness R f c d hj).hom) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1)) :=
  (postnikovCommonRightClassifyingSquare R f c d hj).postcomp
    (Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1))

lemma postnikovCommonRightClassifyingZeroSquare_projection :
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom ≫
      Path.map R (Path.map R (SquareZero.projection _ _)) =
    (postnikovCommonRightClassifyingZeroProjection R f c d hj ≫
      Path.diagonal R (postnikov R (B.obj j).obj 0)) ≫
        Path.diagonal R (Path.algebra R (postnikov R (B.obj j).obj 0)) := by
  let z := postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1
  let t := postnikovTransition R (B.obj j).obj 1 0 (by omega)
  let p := SquareZero.projection (postnikov R (B.obj j).obj 1)
    (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
  have hz : Path.map R (Path.map R z) ≫ Path.map R (Path.map R (SquareZero.projection _ _)) =
      Path.map R (Path.map R p) ≫ Path.map R (Path.map R t) := by
    rw [← Path.map_comp, ← Path.map_comp, ← Path.map_comp, ← Path.map_comp]
    exact congrArg (fun k => Path.map R (Path.map R k))
      (postnikovClassToZeroBase_projection R (B.obj j).obj 1 (by omega) 1)
  have hp : (((postnikovCommonRightBasePath R f c d).postcomp
      (postnikovMap R (B.transition hj).hom 1)).hom ≫ Path.map R t) =
      (postnikovCommonRightBase R f c d ≫ postnikovMap R (B.transition hj).hom 1 ≫ t) ≫
        Path.diagonal R (postnikov R (B.obj j).obj 0) :=
    Path.Witness.hom_eq_constant R
      (((postnikovCommonRightBasePath R f c d).postcomp
        (postnikovMap R (B.transition hj).hom 1)).postcomp t)
  change ((postnikovCommonRightClassifyingSquare R f c d hj).hom ≫
    Path.map R (Path.map R z)) ≫ _ = _
  rw [Category.assoc, hz, ← Category.assoc,
    postnikovCommonRightClassifyingSquare_base_trace]
  simp only [Category.assoc]
  rw [Path.diagonal_naturality]
  rw [reassoc_of% hp]
  rfl

lemma postnikovCommonRightClassifyingZeroSquare_source_trace :
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom ≫
      Path.map R (Path.source R (SquareZero.algebra (postnikov R (B.obj j).obj 0)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) =
    (cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      ((postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovCommonRightBase R f c d) (B.transition hj).hom).precompNonpositiveCell R).hom) ≫
          Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) := by
  change ((postnikovCommonRightClassifyingSquare R f c d hj).hom ≫
    Path.map R (Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1))) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, Path.map_source, Path.map_comp,
    ← Category.assoc, postnikovCommonRightClassifyingSquare_source_trace]

lemma postnikovCommonRightClassifyingZeroSquare_target_trace :
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom ≫
      Path.map R (Path.target R (SquareZero.algebra (postnikov R (B.obj j).obj 0)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) =
    (cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      ((postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovCommonRightDenBase R f c d) (B.transition hj).hom).precompNonpositiveCell
          R).hom) ≫
          Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) := by
  change ((postnikovCommonRightClassifyingSquare R f c d hj).hom ≫
    Path.map R (Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1))) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, Path.map_target, Path.map_comp,
    ← Category.assoc, postnikovCommonRightClassifyingSquare_target_trace]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
