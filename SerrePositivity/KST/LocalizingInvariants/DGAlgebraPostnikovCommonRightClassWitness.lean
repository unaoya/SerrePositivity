module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightStandardClass
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOverImage

/-!
概要：分子側の元の class の右像を、同じ共通底の B の標準 class と実相対経路で比較する。
方針：元の f の class 自然性経路を標準右標的同型で移し、元の係数射を照合する。
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

lemma postnikovCommonRightOver_coefficient :
    postnikovCellClassOverCoefficient R (A.obj i).obj (B.obj i).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom ≫
    (postnikovCommonRightShiftedBaseIso R f c d 1).hom =
      postnikovCommonRightShiftedNumeratorMap R f c d 1 := by
  apply Bimod.Hom.ext
  change (postnikovCellClassOverCoefficient R (A.obj i).obj (B.obj i).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom).hom ≫
      (postnikovCommonRightShiftedBaseIso R f c d 1).hom.hom =
        (postnikovCommonRightShiftedNumeratorMap R f c d 1).hom
  rw [postnikovCommonRightShiftedBaseIso_hom, postnikovCellClassOverCoefficient_hom,
    postnikovCommonRightShiftedNumeratorMap_hom]
  exact Category.comp_id _

lemma postnikovCommonRightClassOver_triangle :
    SquareZero.coefficientMap (postnikovCommonClassBase R f c d)
      (postnikovCellClassOverCoefficient R (A.obj i).obj (B.obj i).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom) ≫
    (postnikovCommonRightClassIso R f c d).hom = postnikovCommonRightClassNumeratorMap R f c d :=
  (SquareZero.coefficientMap_comp _ _).trans
    (congrArg (fun t => SquareZero.coefficientMap (postnikovCommonClassBase R f c d) t)
      (postnikovCommonRightOver_coefficient R f c d))

def postnikovCommonClassTargetRightWitness : Path.Witness R
    (cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) ≫
      postnikovCommonClassTarget R f c d ≫ postnikovCommonRightClassNumeratorMap R f c d)
    (cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) ≫
      postnikovCommonRightStandardClass R f c d) where
  hom := ((postnikovCellClassOverImageWitness R (A.obj i).obj (B.obj i).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom).postcomp
      (postnikovCommonRightClassIso R f c d).hom).hom
  source_eq := by
    rw [((postnikovCellClassOverImageWitness R (A.obj i).obj (B.obj i).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom).postcomp
        (postnikovCommonRightClassIso R f c d).hom).source_eq]
    simp only [Category.assoc]
    rw [postnikovCommonRightClassOver_triangle]
    rfl
  target_eq := by
    rw [((postnikovCellClassOverImageWitness R (A.obj i).obj (B.obj i).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom).postcomp
        (postnikovCommonRightClassIso R f c d).hom).target_eq]
    rfl

lemma postnikovCommonClassTargetRightWitness_relative :
    (postnikovCommonClassTargetRightWitness R f c d).hom ≫
      Path.map R (SquareZero.projection (postnikovCommonClassBase R f c d)
        (DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) 1)) =
    (cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) ≫
      cellAugmentation R (postnikovCommonClassBase R f c d)) ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) := by
  change ((postnikovCellClassOverImageWitness R (A.obj i).obj (B.obj i).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom).hom ≫
      Path.map R (postnikovCommonRightClassIso R f c d).hom) ≫ Path.map R _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightClassIso_projection]
  exact postnikovCellClassOverImageWitness_relative R (A.obj i).obj (B.obj i).obj _ 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
