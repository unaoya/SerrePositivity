module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningTriangleExtensionComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleExtensionVertexRestriction

/-!
概要：元の coherent 三角形の実際の curry 比較成分を始域 fiber へ制限する。
方針：同じ全 pointed 三角形の長辺と普遍 prism に全パラメータの制限式を適用する。
規約：元の三辺と全二単体を保持。使われ方：各点の native 錐と全空間比較の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} (F G J : B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y)
local notation "w" => unstraighteningMappingTriangleLongWitness F G J
  (SSet.const x) (SSet.const y) (SSet.const T.diagonal) T.diagram T.first T.second T.long
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- 元の実際の比較成分を制限すると、同じ全三角形の長辺の指定延長比較になる。 -/
lemma coherentTriangleCurryIso_restrict (b : B _⦋0⦌) :
    HEq
      (VertexIso.map
        ((unstraighteningMappingTriangleIso F G J (SSet.const x) (SSet.const y)
          (SSet.const T.diagonal) T.diagram T.first T.second T.long).app l)
        (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
          (vertexFiberι (leftUnstraighteningProjection F) b)))
      (unstraighteningIdentityRestrictedEndpointIso F J (SSet.const T.diagonal)
        (w).prism (w).source (w).projection l
        (vertexFiberι (leftUnstraighteningProjection F) b)) :=
  unstraighteningMappingTriangleIso_app_pre F G J (SSet.const x) (SSet.const y)
    (SSet.const T.diagonal) T.diagram T.first T.second T.long l
    (vertexFiberι (leftUnstraighteningProjection F) b)

end SerrePositivity.InfinityCategories.F2
