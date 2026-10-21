module

public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedPrismWitnesses
public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedTarget

/-!
概要：元の指定三角形の同じ持ち上げの実中間頂点・実終点を、元の二作用へ厳密に戻す。
方針：元の第一辺と元の全終点の式を、引き戻しの二射影で比較する。
規約：元の選択済み作用と全係数を保持。使われ方：右辺の指定比較の恒等性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "w" => functorTrianglePointedCanonicalWitness T p s hi

/-- 元の指定三角形の第一辺は、元の第一変換の同じ普遍 prism の実制限。 -/
lemma functorTriangleCanonical_first_extension :
    (w).firstWitness.extension = functorHomotopyPointedPrism a s := by
  calc
    _ = (Δ[1] ◁ s) ≫ (stdSimplex.δ (2 : Fin 3) ▷ leftUnstraightening F) ≫
        functorTrianglePointedLift T := by
      apply SSet.hom_ext
      intro n
      rfl
    _ = _ := functorTrianglePointedLift_first T s

/-- 元の指定三角形の実中間頂点は、元の第一作用の後合成そのもの。 -/
lemma functorTriangleCanonical_middle :
    (w).middle = s ≫
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val := by
  have ht := (w).firstWitness.evaluate
  rw [functorTriangleCanonical_first_extension, functorHomotopyPointedPrism_target] at ht
  change s ≫ (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
    pullback.fst pointedSpaceProjection G = (w).middle ≫ pullback.fst pointedSpaceProjection G at ht
  apply pullback.hom_ext
  · exact ht.symm.trans (Category.assoc _ _ _).symm
  · have hp : (s ≫ (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val) ≫
        leftUnstraighteningProjection G = p := by
      rw [Category.assoc,
        (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).property, hi]
    exact (w).middle_projection.trans hp.symm

/-- 元の指定三角形の実終点は、元の二つの選択済み作用の厳密な合成そのもの。 -/
lemma functorTriangleCanonical_endpoint :
    (w).endpoint = s ≫
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
      (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).val := by
  have he : simplexPrismVertex 2 2 C ≫ (w).prism =
      s ≫ simplexPrismVertex 2 2 (leftUnstraightening F) ≫ functorTrianglePointedLift T := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [functorTrianglePointedLift_target] at he
  apply pullback.hom_ext
  · exact (w).endpoint_pointed.symm.trans he
  · have hp : (s ≫
        (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
        (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).val) ≫
        leftUnstraighteningProjection J = p := by
      rw [Category.assoc, Category.assoc,
        (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).property,
        (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).property, hi]
    exact (w).endpoint_projection.trans hp.symm

end SerrePositivity.InfinityCategories.F2
