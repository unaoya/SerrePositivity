module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawFirstChoiceTrianglePrism
public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawConstantInterval

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

/-- 元の全第一辺選択上の同じ長辺を、元の長区間の全定値族に沿う輸送として保持する。 -/
def coherentColimitRawFirstChoiceTriangleLongTransport :
    FiberTransportFamily (b := JoinCocone.vertex (coherentDiagramTotalCocone J))
      pointedSpaceProjection f (intervalMappingUncurry (D : Q ⟶ _)) where
  endpoint := coherentColimitRawFirstChoiceEndpoint B a f ≫ coherentColimitRawFiberTransport B b
  prism := (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ Q)) ≫
    coherentColimitRawFirstChoiceTrianglePrism B T f
  start := coherentColimitRawFirstChoiceTrianglePrism_long_start B T f
  finish := coherentColimitRawFirstChoiceTrianglePrism_long_finish B T f
  over_base := by
    rw [Category.assoc, coherentColimitRawFirstChoiceTrianglePrism_projection,
      coherentColimitRawTriangle_face B d T.diagram 1 T.face_one,
      coherentColimitRawConstantInterval_uncurry, ← Category.assoc, whiskerLeft_fst]

/-- 全長辺輸送の Hom 作用は、元の全第一辺終点へ最後辺輸送を後合成する射そのもの。 -/
lemma coherentColimitRawFirstChoiceTriangleLongTransport_map :
    (coherentColimitRawFirstChoiceTriangleLongTransport B T f).map =
      curry (coherentColimitRawFirstChoiceEndpoint B a f) ≫
        (ihom K).map (coherentColimitRawFiberTransport B b) :=
  curry_natural_right _ _

end SerrePositivity.InfinityCategories.F2
