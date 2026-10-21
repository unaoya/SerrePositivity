module

public import SerrePositivity.InfinityCategories.F2.SmallFiberTriangleLongVertex
public import SerrePositivity.InfinityCategories.F2.CoherentCospanPointedConeLift

/-!
概要：既存の元の prism 制限の底と初期値を、各点の元の三角形へ照合する。
方針：同じ実長辺の二つの射影式を用い、元の底と全円柱を同時に保持する。
規約：元の実延長を選び直さない。使われ方：共通長辺空間への既存の選択空間の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "A" => leftUnstraightening F
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => Over.Hom.left m ≫ lift (𝟙 A) (SSet.const l)
local notation "d" => ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ Δ[0]) ≫
  functorParameterizedPrism (intervalMappingUncurry (SSet.const T.diagonal))
local notation "v" => fst A Δ[0] ≫ 𝟙 A ≫ pullback.fst pointedSpaceProjection F
local notation "w" => unstraighteningMappingTriangleLongWitness F G J (SSet.const x)
  (SSet.const y) (SSet.const T.diagonal) T.diagram T.first T.second T.long

/-- 既存の fiber 制限後の初期値は元の同じ pointed 始点族。 -/
lemma coherentRestrictedPrism_initial : s ≫ v = coherentCospanFiberPointedSource F b := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 既存の制限先の底は、同じ元の二単体の長辺の一点評価そのもの。 -/
lemma coherentRestrictedPrism_base :
    prismParameterRestriction s ≫ d =
      (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ fst Δ[2] a ≫
        coherentTransformationPointDiagram T.diagram (ULift.up b) := by
  calc
    _ = (prismParameterRestriction s ≫ (w).prism) ≫ pointedSpaceProjection := by
      rw [Category.assoc, (w).projection]
    _ = ((stdSimplex.δ (1 : Fin 3) ▷ a) ≫
        coherentSmallFiberPointedTriangle F G J x y T b) ≫ pointedSpaceProjection :=
      congrArg (fun h => h ≫ pointedSpaceProjection)
        (coherentSmallFiberPointedTriangle_long F G J x y T b).symm
    _ = _ := by
      rw [Category.assoc, coherentSmallFiberPointedTriangle_projection]

end SerrePositivity.InfinityCategories.F2
