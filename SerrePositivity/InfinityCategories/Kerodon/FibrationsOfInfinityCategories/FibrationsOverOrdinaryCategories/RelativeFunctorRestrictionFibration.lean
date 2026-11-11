module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorRestrictionLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftKanFibration

/-!
概要：単射による相対関手空間の制限の全ホーン持ち上げ性。
方針：相対内部 Hom の left fibration 性を固定図式へ移し、Kan 性で最後のホーンも充填する。
規約：Fibration はホーンの右持ち上げ性を束縛するためだけに使う。
使われ方：Kerodon §5.3.1（Tag 035D）、有限順序上の strict transport のパラメーター付き比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：left fibration の相対関手空間の単射による制限は left fibration。
方針：相対内部 Hom の left fibration 性を固定した底の図式の部分へ移す。
規約：底の単体集合や図式の始域の quasicategory 性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の末尾への制限のホーン持ち上げ。 -/
instance relativeFunctorPre_leftFibration {A D E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a : A ⟶ B) (i : D ⟶ A) [Mono i] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) where
  mem := by
    let r := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_pullbackObjObjπ i p r
    intro T U j hj
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := r.π) j hj
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.hasLiftingProperty_relativeFunctorPre p a i r j

/-- 概要：単射による相対関手空間の制限は全ホーンを持ち上げる。
方針：相対関手空間の Kan 性と制限の left fibration 性を組み合わせる。
規約：p の left fibration 性と i の単射性だけを要求する。
使われ方：Kerodon §5.3.1（Tag 035D）、制限図式を固定した高次パラメータの持ち上げ。 -/
lemma relativeFunctorPre_fibration {A D E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a : A ⟶ B) (i : D ⟶ A) [Mono i] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.leftFibration_fibration_of_kanComplex _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
