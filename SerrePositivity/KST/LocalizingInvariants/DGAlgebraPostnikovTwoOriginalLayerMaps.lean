module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCoefficientLayerIsos
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellLayerHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassLayerMaps
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassTargetModel

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorOriginalLayerMaps

/-!
概要：二切断候補の元の class 模型への両比較射の H⁻² 作用を計算する。
方針：底変更は係数上で恒等であり、cell から摂動模型への比較も同じ層を保つ。
規約：標的比較の準同型性を仮定しない。使われ方：実 roof 全体の π₂ 作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma sourceToCellModel_layer : homologyMap (d.sourceToCellModel R).hom (-2) ≫
    (postnikovCellModelLayerHomologyIso R (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom =
      (d.sourceLayerIso R).hom ≫
        (d.sourceCoefficientHomologyIso R).hom :=
  PostnikovSuccessorClassInverseData.sourceToCellModel_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToCellModel_layer : homologyMap (d.targetToCellModel R).hom (-2) ≫
    (postnikovCellModelLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
      (d.targetLayerIso R).hom ≫
        (d.targetCoefficientHomologyIso R).hom :=
  PostnikovSuccessorClassInverseData.targetToCellModel_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToOriginalModel_layer : homologyMap (d.sourceToOriginalModel R).hom (-2) ≫
    (postnikovClassModelLayerHomologyIso R (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom =
      (d.sourceLayerIso R).hom ≫
        (d.sourceCoefficientHomologyIso R).hom :=
  PostnikovSuccessorClassInverseData.sourceToOriginalModel_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToOriginalModel_layer : homologyMap (d.targetToOriginalModel R).hom (-2) ≫
    (postnikovClassModelLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
      (d.targetLayerIso R).hom ≫
        (d.targetCoefficientHomologyIso R).hom :=
  PostnikovSuccessorClassInverseData.targetToOriginalModel_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
