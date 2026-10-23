module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanModelFiberInputIso

/-!
概要：元の模型 fiber 比較の入力表示を揃え、元の実際の三 fiber の interval 引き戻しへ写す。
方針：元の比較に入力表示の同型を合成し、二脚と全 path の厳密な一致を計算する。
規約：元の比較・二作用・指定 path を保持。使われ方：実 fiber cospan の end との照合。
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
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "hl" => coherentTransformationTotalMap_projection F X C.toLeft
local notation "hr" => coherentTransformationTotalMap_projection F Y C.toRight
local notation "hf" => coherentTransformationTotalMap_projection X Z C.fromLeft
local notation "hg" => coherentTransformationTotalMap_projection Y Z C.fromRight
local notation "fb" => vertexFiberMap (cf ≫ pZ) pZ cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ pZ) pZ cg rfl b
local notation "ql" => vertexFiberMap pX pZ cf hf b
local notation "qr" => vertexFiberMap pY pZ cg hg b
local notation "m" => coherentCospanConeTotalModelFiberComparison F X Y Z C b

/-- 入力表示だけを同定した、元の同じ実模型 fiber 比較。 -/
def coherentCospanNormalizedModelFiberComparison : vertexFiber pF b ⟶ intervalPullback ql qr :=
  m ≫ (coherentCospanModelInputPullbackIso F X Y Z C b).hom

/-- 入力表示を揃えた比較の第一脚は、元の実際の左 fiber 射である。 -/
lemma coherentCospanNormalizedModelFiberComparison_left :
    coherentCospanNormalizedModelFiberComparison F X Y Z C b ≫ intervalPullbackLeft ql qr =
      vertexFiberMap pF pX cl hl b := by
  rw [coherentCospanNormalizedModelFiberComparison, Category.assoc,
    coherentCospanModelInputPullbackIso_left, ← Category.assoc,
    coherentCospanConeTotalModelFiberComparison_left]
  exact vertexFiberMap_target_projection pF (cf ≫ pZ) pX hf cl
    (by rw [coherentTransformationTotalMap_projection, coherentTransformationTotalMap_projection])
    hl b

/-- 第二脚も元の実際の右 fiber 射である。 -/
lemma coherentCospanNormalizedModelFiberComparison_right :
    coherentCospanNormalizedModelFiberComparison F X Y Z C b ≫ intervalPullbackRight ql qr =
      vertexFiberMap pF pY cr hr b := by
  rw [coherentCospanNormalizedModelFiberComparison, Category.assoc,
    coherentCospanModelInputPullbackIso_right, ← Category.assoc,
    coherentCospanConeTotalModelFiberComparison_right]
  exact vertexFiberMap_target_projection pF (cg ≫ pZ) pY hg cr
    (by rw [coherentTransformationTotalMap_projection, coherentTransformationTotalMap_projection])
    hr b

/-- 元の模型比較の指定 path の全族は、入力表示の同定後も厳密に同じである。 -/
lemma coherentCospanNormalizedModelFiberComparison_path :
    coherentCospanNormalizedModelFiberComparison F X Y Z C b ≫ intervalPullbackPath ql qr =
      m ≫ intervalPullbackPath fb gb := by
  rw [coherentCospanNormalizedModelFiberComparison, Category.assoc,
    coherentCospanModelInputPullbackIso_path]

end SerrePositivity.InfinityCategories.F2
