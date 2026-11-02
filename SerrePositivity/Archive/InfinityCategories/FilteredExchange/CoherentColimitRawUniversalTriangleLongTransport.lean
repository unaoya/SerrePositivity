module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUniversalTrianglePrism

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
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
local notation "H₀₁" => coherentColimitRawTransportPointPrism B a f
local notation "H₁₂" => coherentColimitRawTransportPointPrism B b
  (f ≫ coherentColimitRawFiberTransport B a)
local notation "β" => fst Δ[2] K ≫ FunctorCompositionTriangle.diagram T ≫ coherentColimitFunctor B

local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "q" => fst K (Δ[0] : SSet)
local notation "g" => (f ≫ coherentColimitRawFiberTransport B a) ≫
  coherentColimitRawFiberTransport B b

/-- 元の二普遍辺を持つ同じ全持ち上げの長辺を、元の同じ長区間の全輸送族にする。 -/
def coherentColimitRawUniversalTriangleLongTransport :
    FiberTransportFamily (b := JoinCocone.vertex (coherentDiagramTotalCocone J))
      pointedSpaceProjection f (intervalMappingUncurry D) where
  endpoint := q ≫ g
  prism := (Δ[1] ◁ q) ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫
    coherentColimitRawUniversalTrianglePrism B T f
  start := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      coherentColimitRawUniversalTrianglePrism_long_start]
  finish := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      coherentColimitRawUniversalTrianglePrism_long_finish]
    simp only [Category.assoc]
  over_base := by
    rw [Category.assoc, Category.assoc, coherentColimitRawUniversalTrianglePrism_projection,
      coherentColimitRawTriangle_face B d T.diagram 1 T.face_one,
      coherentColimitRawIntervalVertex_uncurry, ← Category.assoc, whiskerLeft_fst,
      ← Category.assoc, whiskerLeft_fst]

/-- 同じ長区間輸送の一点 prism は、元の同じ全普遍三角形の長辺そのもの。 -/
lemma coherentColimitRawUniversalTriangleLongTransport_point_prism
    (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    (Δ[1] ◁ lift (𝟙 K) (SSet.const v)) ≫
      (coherentColimitRawUniversalTriangleLongTransport B T f).prism =
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ coherentColimitRawUniversalTrianglePrism B T f := by
  change (Δ[1] ◁ lift (𝟙 K) (SSet.const v)) ≫ (Δ[1] ◁ q) ≫ _ = _
  rw [← Category.assoc, ← whiskerLeft_comp, lift_fst, whiskerLeft_id, Category.id_comp]

/-- 同じ長区間輸送の一点終点は、元の二普遍輸送の同じ実合成射。 -/
lemma coherentColimitRawUniversalTriangleLongTransport_point_endpoint
    (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    lift (𝟙 K) (SSet.const v) ≫
      (coherentColimitRawUniversalTriangleLongTransport B T f).endpoint = g := by
  change lift (𝟙 K) (SSet.const v) ≫ q ≫ g = g
  rw [← Category.assoc, lift_fst, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
