module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedTriangleSourceRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallRelativeSourceRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismExtensionRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationPointedTriangle

/-!
概要：小さい始域 fiber の持ち上げ上で元の全 pointed 三角形を保持する。
方針：元の全空間への縮小同型と一点パラメータで、同じ全三角形を制限する。
規約：底の元の二単体と長辺を保持。使われ方：局所指定比較と各点の元の錐の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "C" => vertexFiber (smallLeftUnstraighteningProjection F) b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- 小さい同じ fiber の元の全空間への包含は元の底の同じ点を被覆する。 -/
lemma smallFiberSourceRestriction_projection :
    (m).left ≫ leftUnstraighteningProjection F = SSet.const (ULift.up b) := by
  refine (m).w.trans ?_
  exact (congrArg (fun k => (SSet.uliftFunctor.{u + 1, u}).map k)
    (vertexFiberι_comp (smallLeftUnstraighteningProjection F) b)).trans rfl

/-- 小さい fiber の持ち上げで制限した同じ元の全 pointed 三角形。 -/
def coherentSmallFiberPointedTriangle :
    (Δ[2] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj C ⟶
      PointedSpaceInfinity.{u} :=
  (Δ[2] ◁ lift (m).left (SSet.const l)) ≫
    (coherentTransformationTriangleLift F G J x y T).prism

/-- 全二単体の底は元の指定 coherent 三角形の同じ一点評価。 -/
lemma coherentSmallFiberPointedTriangle_projection :
    coherentSmallFiberPointedTriangle F G J x y T b ≫ pointedSpaceProjection =
      fst (Δ[2] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj C) ≫
        coherentTransformationPointDiagram T.diagram (ULift.up b) :=
  pointedTriangleSourceRestriction_projection (leftUnstraighteningProjection F) (ULift.up b)
    (m).left (smallFiberSourceRestriction_projection F b) T.diagram _
    (coherentTransformationTriangleLift F G J x y T).projection

/-- 小さい fiber 上の同じ全三角形の長辺は、局所比較に使う元の長辺の制限。 -/
lemma coherentSmallFiberPointedTriangle_long :
    (stdSimplex.δ (1 : Fin 3) ▷ (SSet.uliftFunctor.{u + 1, u}).obj C) ≫
      coherentSmallFiberPointedTriangle F G J x y T b =
    prismParameterRestriction ((m).left ≫ lift (𝟙 (leftUnstraightening F)) (SSet.const l)) ≫
      (unstraighteningMappingTriangleLongWitness F G J (SSet.const x) (SSet.const y)
        (SSet.const T.diagonal) T.diagram T.first T.second T.long).prism := by
  rfl

end SerrePositivity.InfinityCategories.F2
