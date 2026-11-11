module

public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceTriangleLongTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawConstantEdgeTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoComponentNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMappingLaws

/-!
概要：元の余極限二単体上で、元の二つの raw 普遍輸送を辺に持つ全三角形を充填する。
方針：同じ普遍 prism の実中間点と元の二面式を使う。
規約：全係数・初期値・元の全二単体を保持。使われ方：新長辺残余の普遍三角形への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
local notation "Q" => coherentColimitRawFirstChoiceSpace B a f
local notation "H₀₁" => coherentColimitRawFirstChoicePrism B a f
local notation "H₁₂" => coherentColimitRawTransportPointPrism B b
  (coherentColimitRawFirstChoiceEndpoint B a f)
local notation "β" => fst Δ[2] (K ⊗ Q) ≫
  FunctorCompositionTriangle.diagram T ≫ coherentColimitFunctor B

local notation "D" => SSet.const (coherentColimitRawIntervalVertex B d)

local notation "m" => curry (coherentColimitRawFirstChoiceEndpoint B a f) ≫
  CategoryTheory.Functor.map (ihom K) (coherentColimitRawFiberTransport B b)
local notation "c" => SSet.const (functorVertex (f ≫ coherentColimitRawFiberTransport B d))

/-- 元の全第一辺選択上で、同じ全長辺と同じ元の固定長辺普遍輸送を比較する指定全同型。 -/
def coherentColimitRawFirstChoiceTriangleComparison : FunctorIso m (c : Q ⟶ _) :=
  functorIsoOfEq
    (FiberTransportFamily.mapIso pointedSpaceProjection f
      (intervalMappingUncurry (D : Q ⟶ _)) (intervalMappingUncurry_one D)
      (coherentColimitRawFirstChoiceTriangleLongTransport B T f)
      (coherentColimitRawConstantEdgeTransport B d f Q))
    (coherentColimitRawFirstChoiceTriangleLongTransport_map B T f)
    (coherentColimitRawConstantEdgeTransport_map B d f Q)

/-- 同じ元の全比較の指定成分。可縮な選択空間と Kan な fiber から直接構成する。 -/
def coherentColimitRawFirstChoiceTriangleComparisonApp
    (x : (coherentColimitRawFirstChoiceSpace B a f) _⦋0⦌) :
    VertexIso ((NatTrans.app m (Opposite.op ⦋0⦌)) x)
      ((NatTrans.app (c : Q ⟶ _) (Opposite.op ⦋0⦌)) x) := by
  have := (coherentColimitRawFirstChoiceSpace_isContractibleKan B a f).kanComplex
  have := vertexFiber_kanComplex_of_leftFibration pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone J))
  exact FunctorIso.app (coherentColimitRawFirstChoiceTriangleComparison B T f) x

/-- 全第一辺選択の任意の二点の元の同型は、同じ指定全長辺比較と可換な正方形をなす。 -/
lemma coherentColimitRawFirstChoiceTriangleComparison_naturality
    {x y : (coherentColimitRawFirstChoiceSpace B a f) _⦋0⦌} (n : VertexIso x y) :
    VertexIso.map n m ≪≫ coherentColimitRawFirstChoiceTriangleComparisonApp B T f y =
      coherentColimitRawFirstChoiceTriangleComparisonApp B T f x ≪≫
        VertexIso.map n (c : Q ⟶ _) := by
  have := (coherentColimitRawFirstChoiceSpace_isContractibleKan B a f).kanComplex
  have := vertexFiber_kanComplex_of_leftFibration pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone J))
  exact functorIso_app_vertexIso_naturality
    (coherentColimitRawFirstChoiceTriangleComparison B T f) n

/-- 元の第一辺終点比較を最後辺輸送で写すと、同じ二つの全長辺比較を厳密に交換する。 -/
lemma coherentColimitRawFirstChoiceTriangleComparison_first_transport
    {x y : (coherentColimitRawFirstChoiceSpace B a f) _⦋0⦌} (n : VertexIso x y) :
    VertexIso.map (VertexIso.map n (curry (coherentColimitRawFirstChoiceEndpoint B a f)))
        (CategoryTheory.Functor.map (ihom K) (coherentColimitRawFiberTransport B b)) ≪≫
      coherentColimitRawFirstChoiceTriangleComparisonApp B T f y =
    coherentColimitRawFirstChoiceTriangleComparisonApp B T f x := by
  have := (coherentColimitRawFirstChoiceSpace_isContractibleKan B a f).kanComplex
  have h := coherentColimitRawFirstChoiceTriangleComparison_naturality B T f n
  rw [VertexIso.map_const, Iso.trans_refl, ← vertexIso_map_comp] at h
  exact h

end SerrePositivity.InfinityCategories.F2
