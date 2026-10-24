module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassBaseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPathComparison

/-!
概要：次段切断逆の class データから、元の係数を持つ三つの実拡大模型を構成する。
方針：同じ共通源上の源 class・係数像 class・標準 class と、その元の実経路を使う。
規約：次段切断との準同型比較と元の逆三角形は別工程。使われ方：実逆の模型上の構成。
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

abbrev classBase := PostnikovCommonCore.postnikovCommonClassBase R hn f d.baseInverse d.layerInverse

abbrev denominatorLayer := PostnikovCommonCore.roofShiftedDenominatorLayer R hn f
  (PostnikovCommonCore.roofRefine R hn f d.baseInverse d.layerInverse.zero.source_le) 1

abbrev numeratorLayer :=
  PostnikovCommonCore.postnikovCommonClassTransitionLayer R hn f d.baseInverse d.layerInverse d.target_le

def classCoefficient : d.denominatorLayer R ⟶ d.numeratorLayer R :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityCoefficient R hn f d.baseInverse d.layerInverse (hj := d.target_le)

def sourceClass : d.classSource R ⟶ SquareZero.algebra (d.classBase R) (d.denominatorLayer R) :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityToCell R hn f d.baseInverse d.layerInverse ≫
    postnikovCellClassOver R (B.obj d.layerInverse.zero.stage).obj (d.classBase R) n hn
      (d.lowerBaseInverse R).roof.denominator

def targetClass : d.classSource R ⟶ SquareZero.algebra (d.classBase R) (d.numeratorLayer R) :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueRight R hn f d.baseInverse d.layerInverse (hj := d.target_le)

def imageClass : d.classSource R ⟶ SquareZero.algebra (d.classBase R) (d.numeratorLayer R) :=
  d.sourceClass R ≫ SquareZero.coefficientMap (d.classBase R) (d.classCoefficient R)

lemma sourceClass_coefficient : d.imageClass R =
    PostnikovCommonCore.postnikovCommonClassStandardGlueLeft R hn f d.baseInverse d.layerInverse (hj := d.target_le) :=
  (PostnikovCommonCore.postnikovCommonClassStandardGlueLeft_eq R hn f d.baseInverse d.layerInverse
    (hj := d.target_le)).symm

/-- 元の class 整合経路を、そのまま cospan 比較の入力にする。 -/
def comparisonPath : Path.Witness R (d.imageClass R)
    (𝟙 (d.classSource R) ≫ d.targetClass R) where
  hom := (d.classWitness R).hom
  source_eq := (d.classWitness R).source_eq.trans (d.sourceClass_coefficient R).symm
  target_eq := (d.classWitness R).target_eq.trans (Category.id_comp _).symm

abbrev sourceModel := HomotopyPullbackModel.algebra R (d.sourceClass R)
  (SquareZero.zeroSection (d.classBase R) (d.denominatorLayer R))

abbrev imageModel := HomotopyPullbackModel.algebra R (d.imageClass R)
  (SquareZero.zeroSection (d.classBase R) (d.numeratorLayer R))

abbrev targetModel := HomotopyPullbackModel.algebra R (d.targetClass R)
  (SquareZero.zeroSection (d.classBase R) (d.numeratorLayer R))

abbrev pathModel := HomotopyPullbackModel.algebra R (MappingPath.target R (d.imageClass R))
  (SquareZero.zeroSection (d.classBase R) (d.numeratorLayer R))

abbrev targetComposedModel :=
  HomotopyPullbackModel.algebra R (𝟙 (d.classSource R) ≫ d.targetClass R)
  (SquareZero.zeroSection (d.classBase R) (d.numeratorLayer R))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
