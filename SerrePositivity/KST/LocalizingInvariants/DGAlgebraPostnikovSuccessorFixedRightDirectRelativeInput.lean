module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectSourceWitness
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeImageWitness
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSourceChange

/-!
概要：元の source 相対模型から、source 模型ホモトピーの実経路と相対 class 入力を構成する。
方針：元の相対模型経路を係数復元で写し、同じ source 自然性の始点へ表示を揃える。
規約：元の相対経路と右脚を保持。使われ方：直接 B 遷移の実模型比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def directRelativeBase :=
  SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) ≫
    PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f d.baseInverse d.layerInverse d.target_le

def directRelativeSourcePath := (d.fixedRightDirectSourceWitness R).precomp
  (SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R))

def directInitialNativeWitness : SquareZero.RelativeWitness (d.directRelativeBase R)
    (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R)
    ((SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
      d.directNativeSource R) ≫ postnikovPerturbedClass R (B.obj j).obj n hn)
    (d.directRelativeBase R ≫ SquareZero.zeroSection (postnikov R (B.obj j).obj n)
      (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R)) :=
  (SquareZeroExtension.relativeImageWitness (d.denominatorLayer R) (d.sourceClass R)
    (PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f d.baseInverse d.layerInverse d.target_le)
    (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R) (d.directNativeClassMap R)
    (hk := d.directNativeClassMap_projection R) (hz := d.directNativeClassMap_zero R)).changeSource
    ((congrArg (fun t => SquareZeroExtension.relativeLeft (d.denominatorLayer R)
      (d.sourceClass R) ≫ t) (d.sourceClass_directNative R)).trans (Category.assoc _ _ _).symm)

lemma directInitialNativeWitness_hom : (d.directInitialNativeWitness R).hom =
    SquareZeroExtension.relativePath (d.denominatorLayer R) (d.sourceClass R) ≫
      Path.map R (d.directNativeClassMap R) := by
  let w := SquareZeroExtension.relativeImageWitness (d.denominatorLayer R) (d.sourceClass R)
    (PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f d.baseInverse d.layerInverse d.target_le)
    (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R) (d.directNativeClassMap R)
    (hk := d.directNativeClassMap_projection R) (hz := d.directNativeClassMap_zero R)
  let hs := (congrArg (fun t => SquareZeroExtension.relativeLeft (d.denominatorLayer R)
    (d.sourceClass R) ≫ t) (d.sourceClass_directNative R)).trans (Category.assoc _ _ _).symm
  let h := SquareZero.RelativeWitness.changeSource_hom w hs
  exact h.trans (SquareZeroExtension.relativeImageWitness_hom (d.denominatorLayer R)
    (d.sourceClass R)
    (PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f d.baseInverse d.layerInverse d.target_le)
    (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R) (d.directNativeClassMap R)
    (hk := d.directNativeClassMap_projection R) (hz := d.directNativeClassMap_zero R))

lemma directRelativeSourcePath_class_relative :
    ((d.directRelativeSourcePath R).postcomp
      (postnikovPerturbedClass R (B.obj j).obj n hn)).hom ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj j).obj n)
        (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R)) =
    d.directRelativeBase R ≫ Path.diagonal R (postnikov R (B.obj j).obj n) := by
  let L := SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R)
  let h := congrArg (fun t => L ≫ t) (d.fixedRightDirectSourceWitness_class_relative R)
  let q := congrArg (fun t => (t ≫ PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f
    d.baseInverse d.layerInverse d.target_le) ≫
      Path.diagonal R (postnikov R (B.obj j).obj n)) (d.sourceRelativeRight_projection R).symm
  change ((L ≫ (d.fixedRightDirectSourceWitness R).hom) ≫ _) ≫ _ = _
  apply Eq.trans ?_ q
  simpa only [Category.assoc] using h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
