module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointHomBasePrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyVertices

/-!
概要：始点 fiber 全体と全左 Hom に同時に依存する、left fibration の実際の輸送作用。
方針：全 Hom の同じ底の円柱を、始点 fiber 全体を係数として一度に持ち上げる。
規約：点ごとに輸送を選ばない。元の持ち上げ円柱の底・両端も保持する。
使われ方：指定した fiber 経路に沿う全 Hom の族の変化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a b : B _⦋0⦌)

/-- 全始点・全 Hom パラメータを一度に保つ、同じ実際の輸送円柱のデータ。 -/
def pointHomFiberTransport :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism a b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fiberTransportFamily p (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism a b)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism_zero a b) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism_one a b)

/-- 全始点と全左 Hom に同時に依存する、終点 fiber への実際の作用。 -/
def pointHomTransportAction : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b :=
  (pointHomFiberTransport p a b).endpoint

/-- 同じ作用を与える、元の全パラメータ輸送円柱。 -/
def pointHomTransportPrism :
    (Δ[1] : SSet.{u}) ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) ⟶ E :=
  (pointHomFiberTransport p a b).prism

/-- 円柱は、全 Hom パラメータを忘れた元の始点の包含から出る。 -/
lemma pointHomTransportPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) ≫ pointHomTransportPrism p a b =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a := by
  simpa only [pointHomTransportPrism, Category.id_comp] using (pointHomFiberTransport p a b).start

/-- 円柱の終点は、同じ全始点・全 Hom の作用そのもの。 -/
lemma pointHomTransportPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) ≫ pointHomTransportPrism p a b =
      pointHomTransportAction p a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b :=
  (pointHomFiberTransport p a b).finish

/-- 全始点の円柱の底は、同じ全 Hom の底の円柱からの厳密な引き戻し。 -/
lemma pointHomTransportPrism_projection :
    pointHomTransportPrism p a b ≫ p =
      (Δ[1] ◁ snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b)) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism a b :=
  (pointHomFiberTransport p a b).over_base

/-- 同じ全 Hom の作用を、一つの始点 fiber 頂点で評価する。 -/
def pointHomTransportActionAt (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b :=
  lift (SSet.const v) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b)) ≫ pointHomTransportAction p a b

/-- 全始点の同じ円柱を一つの始点で制限した円柱。 -/
def pointHomTransportPrismAt (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b ⟶ E :=
  (Δ[1] ◁ lift (SSet.const v) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b))) ≫ pointHomTransportPrism p a b

/-- 同じ始点で制限した円柱の始点は、元の全空間の点そのもの。 -/
lemma pointHomTransportPrismAt_zero (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) ≫ pointHomTransportPrismAt p a b v =
      SSet.const v.val := by
  rw [pointHomTransportPrismAt, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    pointHomTransportPrism_zero, ← Category.assoc, lift_fst, SSet.const_comp]
  rfl

/-- 同じ制限円柱の終点は、その始点で評価した同じ全 Hom の作用。 -/
lemma pointHomTransportPrismAt_one (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) ≫ pointHomTransportPrismAt p a b v =
      pointHomTransportActionAt p a b v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  rw [pointHomTransportPrismAt, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    pointHomTransportPrism_one]
  rfl

/-- 同じ制限円柱も、全く同じ全 Hom の底の円柱を被覆する。 -/
lemma pointHomTransportPrismAt_projection (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    pointHomTransportPrismAt p a b v ≫ p = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism a b := by
  rw [pointHomTransportPrismAt, Category.assoc, pointHomTransportPrism_projection,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, lift_snd,
    whiskerLeft_id, Category.id_comp]

/-- 全始点の作用は、全 Hom から終点 fiber への関手空間への実際の射となる。 -/
def pointHomTransportMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
  curry ((β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)).hom ≫ pointHomTransportAction p a b)

/-- 関手空間の一つの頂点での値は、同じ頂点で評価した全 Hom の作用。 -/
lemma pointHomTransportMap_vertex (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    (pointHomTransportMap p a b).app _ v = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (pointHomTransportActionAt p a b v) := by
  change (pointHomTransportMap p a b).app (Opposite.op ⦋0⦌) v =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) (pointHomTransportActionAt p a b v)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)).symm.injective
  rw [Equiv.symm_apply_apply]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uncurry_at_vertex (pointHomTransportMap p a b) v
  rw [pointHomTransportMap, uncurry_curry] at h
  exact h.symm.trans (by rfl)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
