module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroDiagram
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathSourceMap

/-!
概要：共通零標的で三つの元の class 経路を、同じ非正次数共通源上の両端へ正規化する。
方針：元の標準 class の底変更式と一重・二重 cell 源への比較射を使用する。
規約：元の class と恒等係数の零標的射を保持。使われ方：三経路の貼り合わせ。
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

lemma postnikovCommonRightZeroPathLeft_eq : postnikovCommonRightZeroPathLeft R f c d =
    (cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d := by
  simp only [postnikovCommonRightZeroPathLeft, cellPathNonpositiveComparison_toCell,
    Category.assoc, postnikovCommonRightStandardClass_zero]

lemma postnikovCommonRightZeroPathRight_eq : postnikovCommonRightZeroPathRight R f c d =
    (cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d := by
  simp only [postnikovCommonRightZeroPathRight, cellPathNonpositiveComparison_toCell,
    Category.assoc, postnikovCommonRightDenStandardClass_zero]

abbrev postnikovCommonRightZeroImageSource :=
  (cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
    (postnikovCommonClassSource R f c d ≫ postnikovCommonRightClassNumeratorMap R f c d)) ≫
      postnikovCommonRightClassToZero R f c d

abbrev postnikovCommonRightZeroImageTarget :=
  (cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
    (postnikovCommonClassTarget R f c d ≫ postnikovCommonRightClassNumeratorMap R f c d)) ≫
      postnikovCommonRightClassToZero R f c d

def postnikovCommonRightZeroImageSourceWitness : Path.Witness R
    (postnikovCommonRightZeroImageSource R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) :=
  ((postnikovCommonClassSourceRightWitness R f c d).precompNonpositiveCell R).postcomp
    (postnikovCommonRightClassToZero R f c d)

def postnikovCommonRightZeroImageTargetWitness : Path.Witness R
    (postnikovCommonRightZeroImageTarget R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) :=
  ((postnikovCommonClassTargetRightWitness R f c d).precompNonpositiveCell R).postcomp
    (postnikovCommonRightClassToZero R f c d)

def postnikovCommonRightZeroStandardWitness : Path.Witness R
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) where
  hom := (postnikovCommonRightZeroPathWitness R f c d).hom
  source_eq := (postnikovCommonRightZeroPathWitness R f c d).source_eq.trans
    (postnikovCommonRightZeroPathLeft_eq R f c d)
  target_eq := (postnikovCommonRightZeroPathWitness R f c d).target_eq.trans
    (postnikovCommonRightZeroPathRight_eq R f c d)

lemma postnikovCommonRightZeroImageTarget_projection : postnikovCommonRightZeroImageTarget R f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d := by
  simp only [postnikovCommonRightZeroImageTarget, Category.assoc]
  rw [postnikovCommonRightClassToZero_projection,
    reassoc_of% (postnikovCommonRightClassNumeratorMap_projection R f c d),
    reassoc_of% (postnikovCommonClassTarget_projection R f c d),
    reassoc_of% (cellPathNonpositiveToCell_projection R (postnikovCommonClassBase R f c d))]
  rfl

lemma postnikovCommonRightZeroImageSource_projection : postnikovCommonRightZeroImageSource R f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d := by
  simp only [postnikovCommonRightZeroImageSource, Category.assoc]
  rw [postnikovCommonRightClassToZero_projection,
    reassoc_of% (postnikovCommonRightClassNumeratorMap_projection R f c d),
    reassoc_of% (postnikovCommonClassSource_projection R f c d),
    reassoc_of% (cellPathNonpositiveToCell_projection R (postnikovCommonClassBase R f c d))]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
