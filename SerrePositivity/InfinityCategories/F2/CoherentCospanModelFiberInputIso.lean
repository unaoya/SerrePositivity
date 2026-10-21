module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanConeTotalModelFiber
public import SerrePositivity.InfinityCategories.F2.VertexFiberProjectionIso
public import SerrePositivity.InfinityCategories.F2.IntervalPullbackInputIso

/-!
概要：模型の二入力 fiber の射影表示を、元の X・Y の同じ fiber へ厳密に同定する。
方針：元の全空間作用の射影式を fiber 同型へ渡し、全 path を保つ引き戻し同型を使う。
規約：入力の射影表示の等式と元の二作用を保持。使われ方：実 fiber cospan の end との比較。
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
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "hf" => coherentTransformationTotalMap_projection X Z C.fromLeft
local notation "hg" => coherentTransformationTotalMap_projection Y Z C.fromRight
local notation "fb" => vertexFiberMap (cf ≫ pZ) pZ cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ pZ) pZ cg rfl b
local notation "ql" => vertexFiberMap pX pZ cf hf b
local notation "qr" => vertexFiberMap pY pZ cg hg b

/-- 模型の左入力 fiber と、元の同じ X の fiber の表示同型。 -/
def coherentCospanModelLeftInputFiberIso : vertexFiber (cf ≫ pZ) b ≅ vertexFiber pX b :=
  vertexFiberProjectionIso (cf ≫ pZ) pX hf b

/-- 模型の右入力 fiber と、元の同じ Y の fiber の表示同型。 -/
def coherentCospanModelRightInputFiberIso : vertexFiber (cg ≫ pZ) b ≅ vertexFiber pY b :=
  vertexFiberProjectionIso (cg ≫ pZ) pY hg b

/-- 左の表示同型は、元の同じ左から最後への作用を厳密に保つ。 -/
lemma coherentCospanModelLeftInputFiberIso_arrow :
    (coherentCospanModelLeftInputFiberIso F X Y Z C b).hom ≫ ql = fb :=
  vertexFiberMap_source_projection (cf ≫ pZ) pX pZ hf cf rfl hf b

/-- 右の表示同型も、元の同じ右から最後への作用を保つ。 -/
lemma coherentCospanModelRightInputFiberIso_arrow :
    (coherentCospanModelRightInputFiberIso F X Y Z C b).hom ≫ qr = gb :=
  vertexFiberMap_source_projection (cg ≫ pZ) pY pZ hg cg rfl hg b

/-- 元の模型の path 引き戻しと、元の実際の三 fiber の path 引き戻しの同型。 -/
def coherentCospanModelInputPullbackIso : intervalPullback fb gb ≅ intervalPullback ql qr :=
  intervalPullbackInputIso fb gb ql qr
    (coherentCospanModelLeftInputFiberIso F X Y Z C b)
    (coherentCospanModelRightInputFiberIso F X Y Z C b)
    (coherentCospanModelLeftInputFiberIso_arrow F X Y Z C b)
    (coherentCospanModelRightInputFiberIso_arrow F X Y Z C b)

/-- 元の指定 path の全族を表示同型が厳密に保持する。 -/
lemma coherentCospanModelInputPullbackIso_path :
    (coherentCospanModelInputPullbackIso F X Y Z C b).hom ≫ intervalPullbackPath ql qr =
      intervalPullbackPath fb gb := intervalPullbackInputIsoHom_path _ _ _ _ _ _
    (coherentCospanModelLeftInputFiberIso_arrow F X Y Z C b)
    (coherentCospanModelRightInputFiberIso_arrow F X Y Z C b)

/-- 左入力の元の fiber 表示同型を保持する。 -/
lemma coherentCospanModelInputPullbackIso_left :
    (coherentCospanModelInputPullbackIso F X Y Z C b).hom ≫ intervalPullbackLeft ql qr =
      intervalPullbackLeft fb gb ≫ (coherentCospanModelLeftInputFiberIso F X Y Z C b).hom :=
  intervalPullbackInputIsoHom_left _ _ _ _ _ _
    (coherentCospanModelLeftInputFiberIso_arrow F X Y Z C b)
    (coherentCospanModelRightInputFiberIso_arrow F X Y Z C b)

/-- 右入力の同じ表示同型も保持する。 -/
lemma coherentCospanModelInputPullbackIso_right :
    (coherentCospanModelInputPullbackIso F X Y Z C b).hom ≫ intervalPullbackRight ql qr =
      intervalPullbackRight fb gb ≫ (coherentCospanModelRightInputFiberIso F X Y Z C b).hom :=
  intervalPullbackInputIsoHom_right _ _ _ _ _ _
    (coherentCospanModelLeftInputFiberIso_arrow F X Y Z C b)
    (coherentCospanModelRightInputFiberIso_arrow F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
