module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHom
/-!
概要：元の native Hom の同じ全空間の射を、両変数の全変換へ送る。
方針：既存の全 straightening 関手による同じ底上の射の像を使う。
規約：元の射と指定された射影を保つ。弱同値の仮定は追加しない。
使われ方：IS-W2 R03d の全関手同型を構成するための、同じ全変換の射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open scoped Simplicial
open HomotopicalAlgebra
namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]
local instance jointNativeTransformationModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativeTransformationFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance jointNativeTransformationProjection : LeftFibration (strictBETotJointNativeHomProjection A) :=
  strictBETotJointNativeHomProjection_leftFibration A

/-- 同じ底上の射を元の全分類で送り、同じ raw Hom と native Hom の全変換にする。 -/
def strictBETotJointSourceNativeTransformation
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom) :
    FunctorHom (strictBETotJointRawHomCoherent A) (strictBETotJointNativeHomCoherent A) :=
  (strictBETotJointRawSourceElementsClassificationIso A).hom ≫
    leftStraighteningInfinityDiagramHom
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
      (strictBETotJointNativeHomProjection A) m hm ≫
    (strictBETotJointNativeHomClassificationIso A).hom

end SerrePositivity.EInfinity.BarrattEccles
