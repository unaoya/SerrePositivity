module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightFiberUnitCondition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RightUnitLeftMap

/-!
概要：固定右の随伴単位の空間を元の実単位の母空間に戻す。
方針：元の左写像空間への回収と、固定した右頂点と同じ実単位で引き戻す。
規約：元の e1 の両写像空間と元の単位の全族を使う。
使われ方：元の右ファイバーとの同型の逆射の母空間上の構成。

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

/-- 概要：固定右の単位空間への順比較を含めると、元の coslice 比較。
方針：core と全部分複体の持ち上げの包含を相殺する。
規約：元の実単位の全単体を保つ厳密な等式。
使われ方：往復の射の等式の検証。 -/
lemma rightFiberToAdjointUnitSpace_underlying (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightFiberToAdjointUnitSpace C D w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitUnderlying C D w.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRightFiberToCoslice C D w := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightFiberToAdjointUnitSubspace C D w) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSubspace C D w.val)).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCoslice C D w.val) _).ι = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanCoreMap_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：任意の左関手の族と固定右の合成は、元の右関手による後合成。
方針：族を固定右因子の公式の前に続ける。
規約：パラメータの充填性は仮定しない。
使われ方：同じ実単位を元の対応の母空間へ戻す。 -/
lemma unitComposition_pair_fixedRight {A : SSet.{u + 1}}
    (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D) :
    CartesianMonoidalCategory.lift f (SSet.const w) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D =
      (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftMappingInclusion C D) ≫ (ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w.val) := by
  calc
    _ = (f ≫ CartesianMonoidalCategory.lift (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D)) (SSet.const w)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D := by rw [comp_lift, Category.comp_id, SSet.comp_const]
    _ = _ := by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition_fixedRight, Category.assoc]

/-- 概要：固定右の随伴単位を元の両関手の実単位の母空間へ戻す。
方針：同じ coslice 成分と元の左写像空間の族・固定右頂点の対を引き戻す。
規約：元の実単位の全高次単体を使い、単位を選び直さない。
使われ方：元の右ファイバーへの逆射の指定単位条件を検証する母写像。 -/
def rightAdjointUnitRaw (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w.val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitUnderlying C D w.val ≫
      pullback.fst _ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w.val)))
    (CartesianMonoidalCategory.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitLeft C D w.val) (SSet.const w)) (by
      rw [Category.assoc, pullback.condition]
      calc
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitLeftUnderlying C D w.val ≫
            (ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w.val) := (Category.assoc _ _ _).symm
        _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitLeft C D w.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftMappingInclusion C D) ≫
            (ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w.val) :=
          congrArg (· ≫ (ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w.val))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitLeft_ι C D w.val).symm
        _ = _ := (unitComposition_pair_fixedRight C D w (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitLeft C D w.val)).symm)

/-- 概要：元の母空間へ戻した単位の coslice 成分は同じ実単位の族。
方針：引き戻しの第一射影の計算則。
規約：元の全単体上の厳密な等式。
使われ方：戻した単位の指定単位条件と往復の検証。 -/
lemma rightAdjointUnitRaw_unit (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) :
    rightAdjointUnitRaw C D w ≫ pullback.fst _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitUnderlying C D w.val ≫
      pullback.fst _ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w.val)) :=
  pullback.lift_fst _ _ _

/-- 概要：元の母空間へ戻した底の族は回収した左関手と固定右頂点。
方針：引き戻しの第二射影の計算則。
規約：元の e1 の両写像空間の直積上の等式。
使われ方：戻した左右の関手の保存条件と固定ファイバー条件の回収。 -/
lemma rightAdjointUnitRaw_base (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) :
    rightAdjointUnitRaw C D w ≫ pullback.snd _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D) =
      CartesianMonoidalCategory.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitLeft C D w.val) (SSet.const w) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
