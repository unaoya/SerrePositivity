module
public import SerrePositivity.KST.Fibration.StrictTransportEvaluationPrism
public import SerrePositivity.KST.Fibration.WeakHomotopyAnodyneComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransportEquivalence

/-! # 引き戻した strict section の元の同じ fiber への評価 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 同じ恒等射評価と厳密 fiber 同型で、元の指定 fiber に値を揃える。 -/
def pullbackStrictEvaluationAt {I : Type u} [Category.{u} I] {F B : SSet.{u}}
    (q : F ⟶ B) (k : nerve I ⟶ B) (c : I) (b : B _⦋0⦌)
    (hc : k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) = b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport (pullback.snd q k) c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate (pullback.snd q k) c ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso q k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).hom ≫
      eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q) hc)

/-- 元の fiber へ含めると、同じ評価の後の元の第一射影そのもの。 -/
theorem pullbackStrictEvaluationAt_ι {I : Type u} [Category.{u} I] {F B : SSet.{u}}
    (q : F ⟶ B) (k : nerve I ⟶ B) (c : I) (b : B _⦋0⦌)
    (hc : k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) = b) :
    pullbackStrictEvaluationAt q k c b hc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate (pullback.snd q k) c ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd q k) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) ≫ pullback.fst q k := by
  unfold pullbackStrictEvaluationAt
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberTransport_ι q hc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι]

/-- 引き戻し射影が cocartesian のとき、元の同じ fiber への評価自体は局所化同型。 -/
theorem pullbackStrictEvaluationAt_localized_isIso
    {I : Type u} [Category.{u} I] {F B : SSet.{u}}
    (q : F ⟶ B) (k : nerve I ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.snd q k)]
    (c : I) (b : B _⦋0⦌) (hc : k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) = b) :
    IsIso (AnodyneHomotopy.anodyneQ.map (pullbackStrictEvaluationAt q k c b hc)) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate_isQCatEquivalence (pullback.snd q k) c
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate (pullback.snd q k) c)) :=
    weakHomotopyEquivalence_anodyneQ_isIso _ he.isWeakHomotopyEquivalence
  unfold pullbackStrictEvaluationAt
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration
