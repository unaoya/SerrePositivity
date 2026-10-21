module

public import SerrePositivity.InfinityCategories.F2.SmallTriangleRelativePresentation
public import SerrePositivity.InfinityCategories.F2.RelativeFiberRestriction

/-!
概要：元の指定三角形の比較を同じ fiber 間の実際の関手同型として表示する。
方針：相対比較を fiber Hom へ写し、元の fiber 射の関手頂点へ両端を揃える。
規約：底の quasicategory 性を仮定しない。使われ方：各点の元の錐の可換性の照合。
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
local notation "e" => coherentTransformationTriangleRelativeIso F G J x y T

/-- 元の同じ三角形の指定比較を実際の fiber 射の関手同型にする。 -/
def coherentTransformationTriangleFiberIso :
    FunctorIso
      (vertexFiberMap pF pJ (coherentTransformationTotalMap F J T.diagonal)
        (coherentTransformationTotalMap_projection F J T.diagonal) b)
      (vertexFiberMap pF pJ
        (coherentTransformationTotalMap F G x ≫ coherentTransformationTotalMap G J y)
        (by rw [Category.assoc, coherentTransformationTotalMap_projection,
          coherentTransformationTotalMap_projection]) b) := by
  have hs := relativeFunctorFiberHom_vertex pF pJ b (coherentTransformationTotalMap F J T.diagonal)
    (coherentTransformationTotalMap_projection F J T.diagonal)
  have ht := relativeFunctorFiberHom_vertex pF pJ b
    (coherentTransformationTotalMap F G x ≫ coherentTransformationTotalMap G J y)
    (by rw [Category.assoc, coherentTransformationTotalMap_projection,
      coherentTransformationTotalMap_projection])
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hs)).symm ≪≫
    VertexIso.map e (relativeFunctorFiberHom pF pJ b) ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk ht)

/-- fiber の実際の関手同型から頂点の正規化を外すと元の相対比較の同じ指定像。 -/
lemma coherentTransformationTriangleFiberIso_heq_map :
    HEq (coherentTransformationTriangleFiberIso F G J x y T b)
      (VertexIso.map e (relativeFunctorFiberHom pF pJ b)) := by
  unfold coherentTransformationTriangleFiberIso
  dsimp only
  exact iso_endpoints_heq _ _ _

end SerrePositivity.InfinityCategories.F2
