module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftFiberUnitCondition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftUnitRightMap

/-!
概要：固定左の随伴単位の空間を元の実単位の母空間に戻す。
方針：元の右写像空間への回収と、固定した左頂点と同じ実単位で引き戻す。
規約：元の e1 の両写像空間と元の単位の全族を使う。
使われ方：元の左ファイバーとの同型の逆射の母空間上の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：固定左の単位空間への順比較を含めると、元の coslice 比較。
方針：core と全部分複体の持ち上げの包含を相殺する。
規約：元の実単位の全単体を保つ厳密な等式。
使われ方：往復の射の等式の検証。 -/
lemma leftFiberToAdjointUnitSpace_underlying (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFiberToAdjointUnitSpace C D w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointUnitUnderlying C D w.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitLeftFiberToCoslice C D w := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFiberToAdjointUnitSubspace C D w) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftAdjointUnitSubspace C D w.val)).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftUnitCoslice C D w.val) _).ι = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanCoreMap_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：任意の右関手の族と固定左の合成は元の左関手による前合成。
方針：族を固定左因子の公式の前に続ける。
規約：パラメータの充填性は仮定しない。
使われ方：同じ実単位を元の対応の母空間へ戻す。 -/
lemma unitComposition_pair_fixedLeft {A : SSet.{u + 1}}
    (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C) :
    CartesianMonoidalCategory.lift (SSet.const w) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D =
      (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightMappingInclusion D C) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w.val)).app C.obj := by
  calc
    _ = (f ≫ CartesianMonoidalCategory.lift (SSet.const w) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D := by rw [comp_lift, Category.comp_id, SSet.comp_const]
    _ = _ := by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition_fixedLeft, Category.assoc]

/-- 概要：固定左の随伴単位を元の両関手の実単位の母空間へ戻す。
方針：同じ coslice 成分と元の右写像空間の族・固定左頂点の対を引き戻す。
規約：元の実単位の全高次単体を使い、単位を選び直さない。
使われ方：元の左ファイバーへの逆射の指定単位条件を検証する母写像。 -/
def leftAdjointUnitRaw (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftAdjointUnitSpace C D w.val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointUnitUnderlying C D w.val ≫
      pullback.fst _ ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w.val)).app C.obj))
    (CartesianMonoidalCategory.lift (SSet.const w) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointUnitRight C D w.val)) (by
      rw [Category.assoc, pullback.condition]
      calc
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointUnitRightUnderlying C D w.val ≫
            (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w.val)).app C.obj := (Category.assoc _ _ _).symm
        _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointUnitRight C D w.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightMappingInclusion D C) ≫
            (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w.val)).app C.obj :=
          congrArg (· ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w.val)).app C.obj)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointUnitRight_ι C D w.val).symm
        _ = _ := (unitComposition_pair_fixedLeft C D w (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointUnitRight C D w.val)).symm)

/-- 概要：元の母空間へ戻した単位の coslice 成分は同じ実単位の族。
方針：引き戻しの第一射影の計算則。
規約：元の全単体上の厳密な等式。
使われ方：戻した単位の指定単位条件と往復の検証。 -/
lemma leftAdjointUnitRaw_unit (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D _⦋0⦌) :
    leftAdjointUnitRaw C D w ≫ pullback.fst _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointUnitUnderlying C D w.val ≫
      pullback.fst _ ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w.val)).app C.obj) :=
  pullback.lift_fst _ _ _

/-- 概要：元の母空間へ戻した底は固定左頂点と回収した右関手の対。
方針：引き戻しの第二射影の計算則を使う。
規約：元の e1 の両写像空間の直積上の等式。
使われ方：固定左条件と右関手の保存条件の回収。 -/
lemma leftAdjointUnitRaw_base (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D _⦋0⦌) :
    leftAdjointUnitRaw C D w ≫ pullback.snd _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D) =
      CartesianMonoidalCategory.lift (SSet.const w) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointUnitRight C D w.val) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
