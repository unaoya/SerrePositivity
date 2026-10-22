module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenStandard
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOverImage

/-!
概要：分母側の元の class の右像を、同じ共通底の B の標準 class と実相対経路で比較する。
方針：元の B の遷移の class 自然性経路を標準右標的同型で移し、元の係数射を照合する。
規約：二重 cell augmentation と元の class を保持。使われ方：class 整合の片側の比較。
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
  (d : PostnikovCommonLayerInverse R f c)

lemma postnikovCommonRightDenOver_coefficient :
    postnikovCellClassOverCoefficient R (B.obj d.zero.stage).obj (B.obj i).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom ≫
    (postnikovCommonRightShiftedDenBaseIso R f c d 1).hom =
      postnikovCommonRightShiftedDenominatorMap R f c d 1 := by
  apply Bimod.Hom.ext
  change (postnikovCellClassOverCoefficient R (B.obj d.zero.stage).obj (B.obj i).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom).hom ≫
      (postnikovCommonRightShiftedDenBaseIso R f c d 1).hom.hom =
        (postnikovCommonRightShiftedDenominatorMap R f c d 1).hom
  rw [postnikovCommonRightShiftedDenBaseIso_hom, postnikovCellClassOverCoefficient_hom,
    postnikovCommonRightShiftedDenominatorMap_hom]
  exact Category.comp_id _

lemma postnikovCommonRightDenClassOver_triangle :
    SquareZero.coefficientMap (postnikovCommonClassBase R f c d)
      (postnikovCellClassOverCoefficient R (B.obj d.zero.stage).obj (B.obj i).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom) ≫
    (postnikovCommonRightDenClassIso R f c d).hom =
      postnikovCommonRightClassDenominatorMap R f c d :=
  (SquareZero.coefficientMap_comp _ _).trans
    (congrArg (fun t => SquareZero.coefficientMap (postnikovCommonClassBase R f c d) t)
      (postnikovCommonRightDenOver_coefficient R f c d))

def postnikovCommonClassSourceRightWitness : Path.Witness R
    (cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) ≫
      postnikovCommonClassSource R f c d ≫ postnikovCommonRightClassNumeratorMap R f c d)
    (cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) ≫
      postnikovCommonRightDenStandardClass R f c d) where
  hom := ((postnikovCellClassOverImageWitness R (B.obj d.zero.stage).obj (B.obj i).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom).postcomp
      (postnikovCommonRightDenClassIso R f c d).hom).hom
  source_eq := by
    rw [((postnikovCellClassOverImageWitness R (B.obj d.zero.stage).obj (B.obj i).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom).postcomp
        (postnikovCommonRightDenClassIso R f c d).hom).source_eq]
    simp only [Category.assoc]
    rw [postnikovCommonRightDenClassOver_triangle]
    exact congrArg
      (fun t => cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) ≫ t)
      (postnikovCommonClassSource_right_image R f c d).symm
  target_eq := by
    rw [((postnikovCellClassOverImageWitness R (B.obj d.zero.stage).obj (B.obj i).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom).postcomp
        (postnikovCommonRightDenClassIso R f c d).hom).target_eq]
    rfl

lemma postnikovCommonClassSourceRightWitness_relative :
    (postnikovCommonClassSourceRightWitness R f c d).hom ≫
      Path.map R (SquareZero.projection (postnikovCommonClassBase R f c d)
        (DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) 1)) =
    (cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) ≫
      cellAugmentation R (postnikovCommonClassBase R f c d)) ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) := by
  change ((postnikovCellClassOverImageWitness R (B.obj d.zero.stage).obj (B.obj i).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom).hom ≫
      Path.map R (postnikovCommonRightDenClassIso R f c d).hom) ≫ Path.map R _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightDenClassIso_projection]
  exact postnikovCellClassOverImageWitness_relative R (B.obj d.zero.stage).obj
    (B.obj i).obj _ 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
