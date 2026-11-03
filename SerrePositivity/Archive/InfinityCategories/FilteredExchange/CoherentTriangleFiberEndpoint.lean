module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleFiberIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NormalizedSmallTriangleEndpoint

/-!
概要：元の実際の fiber 間の三角形比較を、同じ二 prism の局所比較へ接続する。
方針：fiber Hom を制限と持ち上げへ分解し、小さい局所比較との等式を適用する。
規約：元の全二単体と指定同型を保持。使われ方：各点の錐の元の可換性との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pJ" => smallLeftUnstraighteningProjection J
local notation "s" => vertexFiberι pF b
local notation "Q" => relativeFunctorBaseFiberHom pJ (s ≫ pF) b (vertexFiberι_comp pF b)
local notation "e" => coherentTransformationTriangleRelativeIso F G J x y T

/-- 実際の fiber 間の指定三角形比較は、同じ局所指定比較を fiber へ写した値。 -/
lemma coherentTransformationTriangleFiberIso_heq_endpoint :
    HEq (coherentTransformationTriangleFiberIso F G J x y T b)
      (VertexIso.map (normalizedSmallTriangleEndpointIso F G J x y T s) Q) := by
  have h := (heq_of_eq (vertexIso_map_comp e (relativeFunctorPre pJ pF s) Q)).trans
    (vertexIso_map_heq e (relativeFunctorFiberHom_eq_restrict pF pJ b))
  rw [coherentSmallTriangleRelativeIso_pre_eq_endpoint F G J x y T s] at h
  exact (coherentTransformationTriangleFiberIso_heq_map F G J x y T b).trans h.symm

end SerrePositivity.InfinityCategories.F2
