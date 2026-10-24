module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreShifted
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFormula

/-!
概要：構成した係数逆を使い、同じ細分 roof 底上に class 比較の両端を実射で置く。
方針：元の分母・分子で cell class を引き戻し、分母側の係数を実逆で移す。
規約：切断次数 n と class の単位 shift 1 を区別する。使われ方：class 整合の両端。
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
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)
  (u : denominatorLayer R hn f c ⟶ numeratorLayer R hn f c)

abbrev classBase := c.roof.apex

local instance classBase_nonpositive : (classBase R f c).X.IsStrictlyLE 0 :=
  c.roof_nonpositive

abbrev classCoefficientMap :
    SquareZero.algebra (classBase R f c)
      (shiftedDenominatorLayer R hn f
        c 1) ⟶
    SquareZero.algebra (classBase R f c)
      (shiftedNumeratorLayer R hn f
        c 1) :=
  SquareZero.coefficientMap _ (shiftedCoefficientMap R hn f c u 1)

lemma classCoefficientMap_projection : classCoefficientMap R hn f c u ≫
    SquareZero.projection _ (shiftedNumeratorLayer R hn f
      c 1) =
    SquareZero.projection _ (shiftedDenominatorLayer R hn f
      c 1) :=
  SquareZero.coefficientMap_projection _ _

abbrev classSource : cellResolution R (classBase R f c) ⟶
    SquareZero.algebra (classBase R f c)
      (shiftedNumeratorLayer R hn f
        c 1) :=
  postnikovCellClassOver R (B.obj m).obj _ n hn
    c.roof.denominator ≫
      classCoefficientMap R hn f c u

abbrev classTarget : cellResolution R (classBase R f c) ⟶
    SquareZero.algebra (classBase R f c)
      (shiftedNumeratorLayer R hn f
        c 1) :=
  postnikovCellClassOver R (A.obj i).obj _ n hn
    c.roof.numerator

lemma classSource_projection : classSource R hn f c u ≫
    SquareZero.projection _ (shiftedNumeratorLayer R hn f
      c 1) =
      cellAugmentation R (classBase R f c) := by
  rw [classSource, Category.assoc,
    classCoefficientMap_projection]
  exact postnikovCellClassOver_projection R (B.obj m).obj _ n hn _

lemma classTarget_projection : classTarget R hn f c ≫
    SquareZero.projection _ (shiftedNumeratorLayer R hn f
      c 1) =
      cellAugmentation R (classBase R f c) :=
  postnikovCellClassOver_projection _ _ _ _ _ _

lemma classSource_coefficient : (classSource R hn f c u).hom ≫
    (biprod.snd : (classBase R f c).X ⊞
      (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧ ⟶
        (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧) =
      (cellResolutionMap R
        c.roof.denominator).hom ≫
      (postnikovCellDerivation R (B.obj m).obj n hn).hom ≫
        u.hom⟦(1 : ℤ)⟧' := by
  have h := postnikovCellClassOver_map_coefficient R (B.obj m).obj
    (classBase R f c) n hn
    c.roof.denominator
    (shiftedCoefficientMap R hn f c u 1)
  exact h.trans (congrArg (fun (t :
    (postnikovLayer R (B.obj m).obj n)⟦(1 : ℤ)⟧ ⟶
      (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧) =>
    (cellResolutionMap R
      c.roof.denominator).hom ≫
    (postnikovCellDerivation R (B.obj m).obj n hn).hom ≫ t)
    (shiftedCoefficientMap_hom R hn f c u 1))

lemma classTarget_coefficient : (classTarget R hn f c).hom ≫
    (biprod.snd : (classBase R f c).X ⊞
      (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧ ⟶
        (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧) =
      (cellResolutionMap R
        c.roof.numerator).hom ≫
      (postnikovCellDerivation R (A.obj i).obj n hn).hom :=
  postnikovCellClassOver_coefficient _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
