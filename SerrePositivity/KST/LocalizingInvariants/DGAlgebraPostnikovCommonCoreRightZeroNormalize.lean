module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroDiagram
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroPath
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

lemma postnikovCommonRightZeroPathLeft_eq : postnikovCommonRightZeroPathLeft R hn f c d =
    (cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d := by
  simp only [postnikovCommonRightZeroPathLeft, cellPathNonpositiveComparison_toCell,
    Category.assoc, postnikovCommonRightStandardClass_zero]

lemma postnikovCommonRightZeroPathRight_eq : postnikovCommonRightZeroPathRight R hn f c d =
    (cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightDenStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d := by
  simp only [postnikovCommonRightZeroPathRight, cellPathNonpositiveComparison_toCell,
    Category.assoc, postnikovCommonRightDenStandardClass_zero]

abbrev postnikovCommonRightZeroImageSource :=
  (cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
    (postnikovCommonClassSource R hn f c d ≫ postnikovCommonRightClassNumeratorMap R hn f c d)) ≫
      postnikovCommonRightClassToZero R hn f c d

abbrev postnikovCommonRightZeroImageTarget :=
  (cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
    (postnikovCommonClassTarget R hn f c d ≫ postnikovCommonRightClassNumeratorMap R hn f c d)) ≫
      postnikovCommonRightClassToZero R hn f c d

def postnikovCommonRightZeroImageSourceWitness : Path.Witness R
    (postnikovCommonRightZeroImageSource R hn f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightDenStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d) :=
  ((postnikovCommonClassSourceRightWitness R hn f c d).precompNonpositiveCell R).postcomp
    (postnikovCommonRightClassToZero R hn f c d)

def postnikovCommonRightZeroImageTargetWitness : Path.Witness R
    (postnikovCommonRightZeroImageTarget R hn f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d) :=
  ((postnikovCommonClassTargetRightWitness R hn f c d).precompNonpositiveCell R).postcomp
    (postnikovCommonRightClassToZero R hn f c d)

def postnikovCommonRightZeroStandardWitness : Path.Witness R
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightDenStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d) where
  hom := (postnikovCommonRightZeroPathWitness R hn f c d).hom
  source_eq := (postnikovCommonRightZeroPathWitness R hn f c d).source_eq.trans
    (postnikovCommonRightZeroPathLeft_eq R hn f c d)
  target_eq := (postnikovCommonRightZeroPathWitness R hn f c d).target_eq.trans
    (postnikovCommonRightZeroPathRight_eq R hn f c d)

lemma postnikovCommonRightZeroImageTarget_projection : postnikovCommonRightZeroImageTarget R hn f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d := by
  simp only [postnikovCommonRightZeroImageTarget, Category.assoc]
  rw [postnikovCommonRightClassToZero_projection,
    reassoc_of% (postnikovCommonRightClassNumeratorMap_projection R hn f c d),
    reassoc_of% (postnikovCommonClassTarget_projection R hn f c d),
    reassoc_of% (cellPathNonpositiveToCell_projection R (postnikovCommonClassBase R hn f c d))]
  rfl

lemma postnikovCommonRightZeroImageSource_projection : postnikovCommonRightZeroImageSource R hn f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d := by
  simp only [postnikovCommonRightZeroImageSource, Category.assoc]
  rw [postnikovCommonRightClassToZero_projection,
    reassoc_of% (postnikovCommonRightClassNumeratorMap_projection R hn f c d),
    reassoc_of% (postnikovCommonClassSource_projection R hn f c d),
    reassoc_of% (cellPathNonpositiveToCell_projection R (postnikovCommonClassBase R hn f c d))]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
