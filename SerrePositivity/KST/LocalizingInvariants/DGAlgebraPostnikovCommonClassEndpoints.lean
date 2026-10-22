module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonShiftedCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFormula

/-!
概要：構成した係数逆を使い、同じ細分 roof 底上に class 比較の両端を実射で置く。
方針：元の分母・分子で cell class を引き戻し、分母側の係数を実逆で移す。
規約：二射を結ぶ乗法的経路は未主張。使われ方：class 整合の証明すべき正確な両端。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

abbrev postnikovCommonClassBase := (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex

def postnikovCommonClassCoefficientMap :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedDenominatorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) :=
  SquareZero.coefficientMap _ (postnikovCommonShiftedCoefficientMap R f c d 1)

lemma postnikovCommonClassCoefficientMap_projection : postnikovCommonClassCoefficientMap R f c d ≫
    SquareZero.projection _ (postnikovOneRoofShiftedNumeratorLayer R f
      (postnikovOneRoofRefine R f c d.zero.source_le) 1) =
    SquareZero.projection _ (postnikovOneRoofShiftedDenominatorLayer R f
      (postnikovOneRoofRefine R f c d.zero.source_le) 1) :=
  SquareZero.coefficientMap_projection _ _

def postnikovCommonClassSource : cellResolution R (postnikovCommonClassBase R f c d) ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) :=
  postnikovCellClassOver R (B.obj d.zero.stage).obj _ 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
      postnikovCommonClassCoefficientMap R f c d

def postnikovCommonClassTarget : cellResolution R (postnikovCommonClassBase R f c d) ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) :=
  postnikovCellClassOver R (A.obj i).obj _ 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator

lemma postnikovCommonClassSource_projection : postnikovCommonClassSource R f c d ≫
    SquareZero.projection _ (postnikovOneRoofShiftedNumeratorLayer R f
      (postnikovOneRoofRefine R f c d.zero.source_le) 1) =
      cellAugmentation R (postnikovCommonClassBase R f c d) := by
  rw [postnikovCommonClassSource, Category.assoc,
    postnikovCommonClassCoefficientMap_projection]
  exact postnikovCellClassOver_projection R (B.obj d.zero.stage).obj _ 1 (by omega) _

lemma postnikovCommonClassTarget_projection : postnikovCommonClassTarget R f c d ≫
    SquareZero.projection _ (postnikovOneRoofShiftedNumeratorLayer R f
      (postnikovOneRoofRefine R f c d.zero.source_le) 1) =
      cellAugmentation R (postnikovCommonClassBase R f c d) :=
  postnikovCellClassOver_projection _ _ _ _ _ _

lemma postnikovCommonClassSource_coefficient : (postnikovCommonClassSource R f c d).hom ≫
    (biprod.snd : (postnikovCommonClassBase R f c d).X ⊞
      (postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧ ⟶
        (postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧) =
      (cellResolutionMap R
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator).hom ≫
      (postnikovCellDerivation R (B.obj d.zero.stage).obj 1 (by omega)).hom ≫
        d.coefficient.hom⟦(1 : ℤ)⟧' := by
  have h := postnikovCellClassOver_map_coefficient R (B.obj d.zero.stage).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
    (postnikovCommonShiftedCoefficientMap R f c d 1)
  exact h.trans (congrArg (fun (t :
    (postnikovLayer R (B.obj d.zero.stage).obj 1)⟦(1 : ℤ)⟧ ⟶
      (postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧) =>
    (cellResolutionMap R
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator).hom ≫
    (postnikovCellDerivation R (B.obj d.zero.stage).obj 1 (by omega)).hom ≫ t)
    (postnikovCommonShiftedCoefficientMap_hom R f c d 1))

lemma postnikovCommonClassTarget_coefficient : (postnikovCommonClassTarget R f c d).hom ≫
    (biprod.snd : (postnikovCommonClassBase R f c d).X ⊞
      (postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧ ⟶
        (postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧) =
      (cellResolutionMap R
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator).hom ≫
      (postnikovCellDerivation R (A.obj i).obj 1 (by omega)).hom :=
  postnikovCellClassOver_coefficient _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
