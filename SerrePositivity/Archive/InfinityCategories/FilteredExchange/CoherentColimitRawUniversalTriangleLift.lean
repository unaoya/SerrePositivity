module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawTriangleFace
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawTransportPointPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.F1DiagramsTrianglePrism

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

/-- 元の指定二単体上に、同じ初期値から元の二つの raw 普遍輸送を持つ全持ち上げがある。 -/
lemma exists_coherentColimitRawUniversalTriangleLift :
    ∃ W : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u},
      (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ W = H₀₁ ∧
      (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ W = H₁₂ ∧ W ≫ pointedSpaceProjection = β := by
  have hw : prismEndpoint 1 K ≫ H₀₁ = prismEndpoint 0 K ≫ H₁₂ := by
    rw [coherentColimitRawTransportPointPrism_finish, coherentColimitRawTransportPointPrism_start]
  have hfirst : H₀₁ ≫ pointedSpaceProjection =
      (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ β :=
    (coherentColimitRawTransportPointPrism_projection B a f).trans
      (coherentColimitRawTriangle_face B a T.diagram 2 T.face_two).symm
  have hlast : H₁₂ ≫ pointedSpaceProjection =
      (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ β :=
    (coherentColimitRawTransportPointPrism_projection B b _).trans
      (coherentColimitRawTriangle_face B b T.diagram 0 T.face_zero).symm
  exact innerFibration_fillTrianglePrism pointedSpaceProjection H₀₁ H₁₂ β hw hfirst hlast

end SerrePositivity.InfinityCategories.F2
