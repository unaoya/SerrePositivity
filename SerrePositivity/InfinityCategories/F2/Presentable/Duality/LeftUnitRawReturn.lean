module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftFiberUnitCondition
public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitRightMap

/-!
概要：固定左の随伴単位の空間を元の実単位の母空間に戻す。
方針：元の右写像空間への回収と、固定した左頂点と同じ実単位で引き戻す。
規約：元の e1 の両写像空間と元の単位の全族を使う。
使われ方：元の左ファイバーとの同型の逆射の母空間上の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：固定左の単位空間への順比較を含めると、元の coslice 比較。
方針：core と全部分複体の持ち上げの包含を相殺する。
規約：元の実単位の全単体を保つ厳密な等式。
使われ方：往復の射の等式の検証。 -/
lemma leftFiberToAdjointUnitSpace_underlying (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftFiberToAdjointUnitSpace C D w ≫ leftAdjointUnitUnderlying C D w.val =
      adjointUnitLeftFiberToCoslice C D w := by
  change kanCoreMap (leftFiberToAdjointUnitSubspace C D w) ≫
    (quasicategoryCore (LeftAdjointUnitSubspace C D w.val)).ι ≫
      (fullSubcomplexOnVertices (LeftUnitCoslice C D w.val) _).ι = _
  rw [← Category.assoc, kanCoreMap_ι]
  exact fullSubcomplexLift_ι _ _ _

/-- 概要：任意の右関手の族と固定左の合成は元の左関手による前合成。
方針：族を固定左因子の公式の前に続ける。
規約：パラメータの充填性は仮定しない。
使われ方：同じ実単位を元の対応の母空間へ戻す。 -/
lemma unitComposition_pair_fixedLeft {A : SSet.{u + 1}}
    (C D : PresentableInfinityObject.{u}) (w : PrLMappingSpace C D _⦋0⦌)
    (f : A ⟶ PrRMappingSpace D C) :
    CartesianMonoidalCategory.lift (SSet.const w) f ≫ unitComposition C D =
      (f ≫ rightMappingInclusion D C) ≫ (pre (leftVertexFunctor w.val)).app C.obj := by
  calc
    _ = (f ≫ CartesianMonoidalCategory.lift (SSet.const w) (𝟙 (PrRMappingSpace D C))) ≫
        unitComposition C D := by rw [comp_lift, Category.comp_id, SSet.comp_const]
    _ = _ := by rw [Category.assoc, unitComposition_fixedLeft, Category.assoc]

/-- 概要：固定左の随伴単位を元の両関手の実単位の母空間へ戻す。
方針：同じ coslice 成分と元の右写像空間の族・固定左頂点の対を引き戻す。
規約：元の実単位の全高次単体を使い、単位を選び直さない。
使われ方：元の左ファイバーへの逆射の指定単位条件を検証する母写像。 -/
def leftAdjointUnitRaw (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    LeftAdjointUnitSpace C D w.val ⟶ RawAdjointUnitSpace C D :=
  pullback.lift
    (leftAdjointUnitUnderlying C D w.val ≫
      pullback.fst _ ((pre (leftVertexFunctor w.val)).app C.obj))
    (CartesianMonoidalCategory.lift (SSet.const w) (leftAdjointUnitRight C D w.val)) (by
      rw [Category.assoc, pullback.condition]
      calc
        _ = leftAdjointUnitRightUnderlying C D w.val ≫
            (pre (leftVertexFunctor w.val)).app C.obj := (Category.assoc _ _ _).symm
        _ = (leftAdjointUnitRight C D w.val ≫ rightMappingInclusion D C) ≫
            (pre (leftVertexFunctor w.val)).app C.obj :=
          congrArg (· ≫ (pre (leftVertexFunctor w.val)).app C.obj)
            (leftAdjointUnitRight_ι C D w.val).symm
        _ = _ := (unitComposition_pair_fixedLeft C D w (leftAdjointUnitRight C D w.val)).symm)

/-- 概要：元の母空間へ戻した単位の coslice 成分は同じ実単位の族。
方針：引き戻しの第一射影の計算則。
規約：元の全単体上の厳密な等式。
使われ方：戻した単位の指定単位条件と往復の検証。 -/
lemma leftAdjointUnitRaw_unit (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftAdjointUnitRaw C D w ≫ pullback.fst _ (unitComposition C D) =
    leftAdjointUnitUnderlying C D w.val ≫
      pullback.fst _ ((pre (leftVertexFunctor w.val)).app C.obj) :=
  pullback.lift_fst _ _ _

/-- 概要：元の母空間へ戻した底は固定左頂点と回収した右関手の対。
方針：引き戻しの第二射影の計算則を使う。
規約：元の e1 の両写像空間の直積上の等式。
使われ方：固定左条件と右関手の保存条件の回収。 -/
lemma leftAdjointUnitRaw_base (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftAdjointUnitRaw C D w ≫ pullback.snd _ (unitComposition C D) =
      CartesianMonoidalCategory.lift (SSet.const w) (leftAdjointUnitRight C D w.val) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
