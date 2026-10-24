module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreShiftedInverse
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

abbrev postnikovCommonClassBase := (roofRefine R hn f c d.zero.source_le).roof.apex

def postnikovCommonClassCoefficientMap :
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (roofShiftedDenominatorLayer R hn f
        (roofRefine R hn f c d.zero.source_le) 1) ⟶
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (roofShiftedNumeratorLayer R hn f
        (roofRefine R hn f c d.zero.source_le) 1) :=
  SquareZero.coefficientMap _ (postnikovCommonShiftedCoefficientMap R hn f c d 1)

lemma postnikovCommonClassCoefficientMap_projection : postnikovCommonClassCoefficientMap R hn f c d ≫
    SquareZero.projection _ (roofShiftedNumeratorLayer R hn f
      (roofRefine R hn f c d.zero.source_le) 1) =
    SquareZero.projection _ (roofShiftedDenominatorLayer R hn f
      (roofRefine R hn f c d.zero.source_le) 1) :=
  SquareZero.coefficientMap_projection _ _

def postnikovCommonClassSource : cellResolution R (postnikovCommonClassBase R hn f c d) ⟶
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (roofShiftedNumeratorLayer R hn f
        (roofRefine R hn f c d.zero.source_le) 1) :=
  postnikovCellClassOver R (B.obj d.zero.stage).obj _ n hn
    (roofRefine R hn f c d.zero.source_le).roof.denominator ≫
      postnikovCommonClassCoefficientMap R hn f c d

def postnikovCommonClassTarget : cellResolution R (postnikovCommonClassBase R hn f c d) ⟶
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (roofShiftedNumeratorLayer R hn f
        (roofRefine R hn f c d.zero.source_le) 1) :=
  postnikovCellClassOver R (A.obj i).obj _ n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator

lemma postnikovCommonClassSource_projection : postnikovCommonClassSource R hn f c d ≫
    SquareZero.projection _ (roofShiftedNumeratorLayer R hn f
      (roofRefine R hn f c d.zero.source_le) 1) =
      cellAugmentation R (postnikovCommonClassBase R hn f c d) := by
  rw [postnikovCommonClassSource, Category.assoc,
    postnikovCommonClassCoefficientMap_projection]
  exact postnikovCellClassOver_projection R (B.obj d.zero.stage).obj _ n hn _

lemma postnikovCommonClassTarget_projection : postnikovCommonClassTarget R hn f c d ≫
    SquareZero.projection _ (roofShiftedNumeratorLayer R hn f
      (roofRefine R hn f c d.zero.source_le) 1) =
      cellAugmentation R (postnikovCommonClassBase R hn f c d) :=
  postnikovCellClassOver_projection _ _ _ _ _ _

lemma postnikovCommonClassSource_coefficient : (postnikovCommonClassSource R hn f c d).hom ≫
    (biprod.snd : (postnikovCommonClassBase R hn f c d).X ⊞
      (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧ ⟶
        (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧) =
      (cellResolutionMap R
        (roofRefine R hn f c d.zero.source_le).roof.denominator).hom ≫
      (postnikovCellDerivation R (B.obj d.zero.stage).obj n hn).hom ≫
        d.coefficient.hom⟦(1 : ℤ)⟧' := by
  have h := postnikovCellClassOver_map_coefficient R (B.obj d.zero.stage).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.denominator
    (postnikovCommonShiftedCoefficientMap R hn f c d 1)
  exact h.trans (congrArg (fun (t :
    (postnikovLayer R (B.obj d.zero.stage).obj n)⟦(1 : ℤ)⟧ ⟶
      (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧) =>
    (cellResolutionMap R
      (roofRefine R hn f c d.zero.source_le).roof.denominator).hom ≫
    (postnikovCellDerivation R (B.obj d.zero.stage).obj n hn).hom ≫ t)
    (postnikovCommonShiftedCoefficientMap_hom R hn f c d 1))

lemma postnikovCommonClassTarget_coefficient : (postnikovCommonClassTarget R hn f c d).hom ≫
    (biprod.snd : (postnikovCommonClassBase R hn f c d).X ⊞
      (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧ ⟶
        (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧) =
      (cellResolutionMap R
        (roofRefine R hn f c d.zero.source_le).roof.numerator).hom ≫
      (postnikovCellDerivation R (A.obj i).obj n hn).hom :=
  postnikovCellClassOver_coefficient _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
