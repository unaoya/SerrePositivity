module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanModelNativeEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection

/-!
概要：各点の元の coherent な錐の極限性から、元の小さい実模型 fiber 比較の同値性を証明。
方針：native 切断への同じ比較の同値を消去し、宇宙持ち上げと入力表示同型を反映する。
規約：元の比較射を保持。使われ方：一般 coherent filtered 図式の引き戻し交換。
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
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local instance : KanComplex (Limits.pullback f g) :=
  HomotopyLimits.kanComplex_of_iso (relativeCospanSectionsIso pointedSpaceProjection d)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "fb" => vertexFiberMap (cf ≫ pZ) pZ cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ pZ) pZ cg rfl b
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "n" => coherentCospanNormalizedModelFiberComparison F X Y Z C b
local instance : KanComplex (vertexFiber pF b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pX b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pY b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration _ _

/-- 各点の元の native 錐が極限なら、正規化した元の小さい模型比較が同値。 -/
lemma coherentCospanNormalizedModelFiberComparison_homotopyEquivalence (hc : IsLimitCone c) :
    IsSimplicialHomotopyEquivalence n := by
  have hM := coherentCospanModelNativeComparison_homotopyEquivalence F X Y Z C b hc
  have hK := coherentCospanNativeIntervalComparison_homotopyEquivalence F X Y Z C b
  have h := hK.isQCatEquivalence.cancel_right hM.isQCatEquivalence
  exact ((isQCatEquivalence_ulift_iff_of_kan n).mp h).isSimplicialHomotopyEquivalence

/-- 入力 fiber の表示も元へ戻すと、元の実模型 fiber 比較そのものが同値である。 -/
lemma coherentCospanConeTotalModelFiberComparison_homotopyEquivalence (hc : IsLimitCone c) :
    IsSimplicialHomotopyEquivalence
      (coherentCospanConeTotalModelFiberComparison F X Y Z C b) := by
  let e := coherentCospanModelInputPullbackIso F X Y Z C b
  have : KanComplex (intervalPullback fb gb) := HomotopyLimits.kanComplex_of_iso e.symm
  have h := coherentCospanNormalizedModelFiberComparison_homotopyEquivalence F X Y Z C b hc
  exact (HomotopyLimits.homotopyEquivalence_of_isIso e.hom).cancel_right h

end SerrePositivity.InfinityCategories.F2
