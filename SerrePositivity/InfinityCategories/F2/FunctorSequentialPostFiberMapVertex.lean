module

public import SerrePositivity.InfinityCategories.F2.ConstantUnstraighteningFiberMapVertex
public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyRelativePost

/-!
概要：元の二つの相対後合成の実終点を、任意の fiber 射への作用として計算する。
方針：任意の元の相対始点射上で二つの実作用を合成し、定値射影で評価する。
規約：三実射と全係数を保持。使われ方：定値三角形の元の終点の型付き照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 二つの相対後合成の固定値への像は、元の二実作用と始点射の合成の頂点。 -/
lemma functorSequentialPost_fiberMap_vertex {B C X : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} {z : SpaceInfinity.{u} _⦋0⦌}
    (H : SSet.Homotopy F G) (K : SSet.Homotopy G (SSet.const z))
    (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
    (hs : s ≫ leftUnstraighteningProjection F = p)
    (g : vertexFiber pointedSpaceProjection z ⟶ X) :
    ((constantUnstraighteningRelativeIso p z).hom ≫ (ihom C).map g).app (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost K p).app (Opposite.op ⦋0⦌)
        ((functorHomotopyRelativePost H p).app (Opposite.op ⦋0⦌)
          (relativeFunctorVertex (leftUnstraighteningProjection F) p s hs))) =
      functorVertex (((s ≫ ((leftUnstraighteningMappingVertexMap F G
        (coherentVertexOfHomotopy H)).val ≫ (leftUnstraighteningMappingVertexMap G (SSet.const z)
          (coherentVertexOfHomotopy K)).val)) ≫
          constantUnstraighteningFiberProjection B z) ≫ g) := by
  let f := (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
  let k := (leftUnstraighteningMappingVertexMap G (SSet.const z) (coherentVertexOfHomotopy K)).val
  have hp : (s ≫ (f ≫ k)) ≫ leftUnstraighteningProjection (SSet.const z) = p := by
    rw [Category.assoc, Category.assoc,
      (leftUnstraighteningMappingVertexMap G (SSet.const z) (coherentVertexOfHomotopy K)).property,
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property, hs]
  have hx : (functorHomotopyRelativePost K p).app (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost H p).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (leftUnstraighteningProjection F) p s hs)) =
    relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z)) p (s ≫ (f ≫ k)) hp := by
    apply Subtype.ext
    rfl
  rw [hx, constantUnstraighteningRelativeIso_fiberMap_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2
