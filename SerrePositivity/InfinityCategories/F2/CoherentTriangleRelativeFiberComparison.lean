module

public import SerrePositivity.InfinityCategories.F2.CoherentTriangleCurryFiberComparison
public import SerrePositivity.InfinityCategories.F2.RelativeTriangleVertexPresentation

/-!
概要：元の coherent 三角形の相対頂点比較を同じ二 prism の比較へ制限する。
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
lemma coherentTriangleRelativeVertexIso_restrict (b : B _⦋0⦌) :
    HEq
      (VertexIso.map
        (unstraighteningTriangleRelativeVertexIso F G J x y T.diagonal
          T.diagram T.first T.second T.long)
        (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
          (vertexFiberι (leftUnstraighteningProjection F) b)))
      (unstraighteningIdentityRestrictedEndpointIso F J (SSet.const T.diagonal)
        (w).prism (w).source (w).projection l
        (vertexFiberι (leftUnstraighteningProjection F) b)) := by
  have h := unstraighteningTriangleRelativeVertexIso_map_pre_heq_component F G J
    x y T.diagonal T.diagram T.first T.second T.long
    (vertexFiberι (leftUnstraighteningProjection F) b)
  exact h.trans (coherentTriangleCurryIso_restrict F G J x y T b)

end SerrePositivity.InfinityCategories.F2
