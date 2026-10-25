module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairUnitHomFamily

/-!
概要：両変数に自然な単位空間の族を、元の一つの左関手に制限する。
方針：元の left fibration の底変換と curry の頂点公式を接続する。
規約：対象ごとの無関係な族を選ばず、構成した同じ全関手族を制限する。
使われ方：固定左の普遍単位の表現可能性への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の左関手を固定して右関手を全体で動かす底の射。
方針：元の左頂点の定値写像と右側の恒等写像を組にする。
規約：全右関手圏を始域にする。
使われ方：単位空間の left fibration の制限。 -/
def pairFixedLeftBase {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) :
    PrRFunctorSpace D C ⟶ PrLFunctorSpace C D ⊗ PrRFunctorSpace D C :=
  lift (SSet.const v) (𝟙 _)

/-- 概要：固定左での元の二変数合成は、その左関手による前合成。
方針：全部分圏の包含を積の評価に通し、固定左の内部 Hom 合成公式を使う。
規約：右関手の全自然変換を保持する。
使われ方：全単位族の固定左 coslice への比較。 -/
lemma pairFixedLeftBase_composition {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) :
    pairFixedLeftBase v ≫ pairUnitComposition C D =
      rightFunctorInclusion D C ≫ (pre (leftVertexFunctor v)).app C.obj := by
  have hv : (leftFunctorInclusion C D).app (Opposite.op ⦋0⦌) v =
      functorVertex (leftVertexFunctor v) :=
    ((functorVertexEquiv C.obj D.obj).apply_symm_apply v.val).symm
  unfold pairFixedLeftBase pairUnitComposition
  rw [← Category.assoc, lift_map, SSet.const_comp, Category.id_comp, hv]
  rw [← internalHomComposition_fixedLeft (Z := C.obj) (leftVertexFunctor v),
    ← Category.assoc, comp_lift, SSet.comp_const, Category.comp_id]

/-- 概要：元の左関手に制限した実単位空間の同じ分類図式。
方針：全二変数族に底の射の宇宙持ち上げを前合成する。
規約：元の分類関手を選び直さない。
使われ方：固定左の随伴単位の表現可能性。 -/
def pairUnitHomAtLeft {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (PrRFunctorSpace D C) ⟶ SpaceInfinity.{u + 1} :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map (pairFixedLeftBase v) ≫ pairUnitHomBifunctor C D

/-- 概要：元の全関手族の頂点は、同じ二変数族を元の左関手へ制限した図式。
方針：curry の頂点公式と積・宇宙持ち上げの実際の同型を計算する。
規約：図式の自然同型ではなく元の頂点の等式。
使われ方：固定左の普遍単位を全左関手族に戻す。 -/
lemma pairUnitHomFamily_vertex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) :
    (pairUnitHomFamily C D).app (Opposite.op ⦋0⦌) (ULift.up v) =
      functorVertex (pairUnitHomAtLeft v) := by
  have h := (functorVertex_uncurry_at_vertex (pairUnitHomFamily C D) (ULift.up v)).symm
  refine h.trans ?_
  apply congrArg functorVertex
  change lift (𝟙 _) (SSet.const (ULift.up v)) ≫
    uncurry (curry (pairUnitJointEvaluation C D)) = pairUnitHomAtLeft v
  rw [uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：固定左への元の分類図式の制限は、同じ射影の底変換の分類と自然同型。
方針：既存の left fibration 分類の底変換同型を同じ射に適用する。
規約：主経路に新しい分類定理の存在を仮定しない。
使われ方：固定左 coslice の普遍単位との照合。 -/
def pairUnitHomAtLeft_classificationIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) :
    FunctorIso (pairUnitHomAtLeft v)
      (leftStraighteningInfinityDiagram
        (pullback.snd (covariantPairUnitProjection C D) (pairFixedLeftBase v))) := by
  letI : LeftFibration (pullback.snd (covariantPairUnitProjection C D) (pairFixedLeftBase v)) :=
    ⟨leftFibrations.pullback_snd _ _
      (LeftFibration.mem (p := covariantPairUnitProjection C D))⟩
  exact leftStraighteningInfinityDiagram_baseChangeIso
    (covariantPairUnitProjection C D) (pairFixedLeftBase v)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
