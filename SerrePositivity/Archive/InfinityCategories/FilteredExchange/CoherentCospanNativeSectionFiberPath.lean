module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeCommonFinalFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SmallUnstraighteningFunctorIso

/-!
概要：同じ native 全錐の共通終点を通じ、元の左右の実際の fiber 合成の指定同型を作る。
方針：左右の同じ全三角形比較の終点像を、厳密に共通な fiber 写像で合成して下降する。
規約：別の path を選択しない。使われ方：切断の引き戻しと元の模型 path の指定類の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "fl" => vertexFiberMap pF pX (coherentTransformationTotalMap F X C.toLeft)
  (coherentTransformationTotalMap_projection F X C.toLeft) b
local notation "fr" => vertexFiberMap pF pY (coherentTransformationTotalMap F Y C.toRight)
  (coherentTransformationTotalMap_projection F Y C.toRight) b
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration _ _

/-- 同じ全 native 錐の厳密に共通な終点を通る、元の左右の fiber 合成の指定比較。 -/
def coherentCospanNativeSectionFiberPathIso :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map (fl ≫ ql))
      ((SSet.uliftFunctor.{u + 1, u}).map (fr ≫ qr)) :=
  (coherentCospanNativeLeftFinalFiberIso F X Y Z C b).symm ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk (congrArg functorVertex
      (coherentCospanNativeFinalFiberMap_eq F X Y Z C b))) ≪≫
        coherentCospanNativeRightFinalFiberIso F X Y Z C b

/-- 共通終点を通る同じ指定比較を、元の小さい fiber 間の同型へ下降する。 -/
def coherentCospanNativeSectionFiberPathDownIso : FunctorIso (fl ≫ ql) (fr ≫ qr) :=
  functorIsoDown (coherentCospanNativeSectionFiberPathIso F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
