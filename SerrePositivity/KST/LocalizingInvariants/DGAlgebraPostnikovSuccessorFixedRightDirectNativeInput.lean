module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectClassRestore
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorSourceModelProjections

/-!
概要：元の分母相対模型の class と経路を、元の Bⱼ の平方零標的へ送る射を構成する。
方針：係数復元と元の直接 B 遷移を同一視し、元の零切断と source class を保つ。
規約：元の係数と sourceCellMap を保持。使われ方：source 模型ホモトピーの実入力。
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

abbrev directNativeLayer := postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1

def directNativeClassMap : SquareZero.algebra (d.classBase R) (d.denominatorLayer R) ⟶
    postnikovDerivationTarget R (B.obj j).obj n hn :=
  SquareZero.coefficientMap (d.classBase R) (d.rightDenominatorCoefficient R) ≫
    d.rightDenominatorClassRestore R

lemma directNativeClassMap_projection : d.directNativeClassMap R ≫
    SquareZero.projection (postnikov R (B.obj j).obj n) (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R) =
    SquareZero.projection (d.classBase R) (d.denominatorLayer R) ≫
      PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f d.baseInverse d.layerInverse d.target_le := by
  rw [directNativeClassMap, Category.assoc, rightDenominatorClassRestore,
    SquareZero.coefficientRestore_projection, ← Category.assoc,
    SquareZero.coefficientMap_projection]

lemma directNativeClassMap_zero : SquareZero.zeroSection (d.classBase R) (d.denominatorLayer R) ≫
    d.directNativeClassMap R =
    PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f d.baseInverse d.layerInverse d.target_le ≫
      SquareZero.zeroSection (postnikov R (B.obj j).obj n)
        (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R) := by
  rw [directNativeClassMap, ← Category.assoc, SquareZero.zeroSection_coefficientMap]
  exact SquareZero.coefficientRestore_zeroSection _ _ _

def directNativeSource := d.sourceCellMap R ≫
  postnikovCellLift R (B.obj d.layerInverse.zero.stage).obj n hn ≫
    postnikovPerturbedMap R
      (PostnikovCommonCore.postnikovCommonRightDenDirectMap R hn f d.baseInverse d.layerInverse d.target_le) n hn

lemma sourceClass_directNative : d.sourceClass R ≫ d.directNativeClassMap R =
    d.directNativeSource R ≫ postnikovPerturbedClass R (B.obj j).obj n hn := by
  let g := postnikovDerivationTargetMap R
    (PostnikovCommonCore.postnikovCommonRightDenDirectMap R hn f d.baseInverse d.layerInverse d.target_le) n hn
  calc
    _ = (d.sourceClass R ≫ SquareZero.baseChangeMap (d.lowerBaseInverse R).roof.denominator
        (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj n hn 1)) ≫
          g := (congrArg (fun t => d.sourceClass R ≫ t)
            (d.rightDenominatorCoefficient_restore R)).trans (Category.assoc _ _ _).symm
    _ = (d.sourceCellMap R ≫
        postnikovCellClass R (B.obj d.layerInverse.zero.stage).obj n hn) ≫ g :=
      congrArg (fun t => t ≫ g) (d.sourceClass_baseChange R)
    _ = _ := by
      simp only [g, directNativeSource, postnikovCellClass, Category.assoc,
        postnikovPerturbedClass_naturality]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
