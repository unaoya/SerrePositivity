module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace

/-!
概要：coherent な関手の族を指定頂点のグラフで制限すると、同じ頂点の関手を得る。
方針：定値射による前合成と uncurry の自然性を用い、対角射で回収する。
規約：頂点の関手への対応は既存の全単射に固定する。
使われ方：元の前層図式の共同評価と、その指定した値の照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ族の頂点のグラフに沿う制限は、元の頂点に対応する関手。 -/
lemma uncurry_graph_vertex {X Y Z : SSet.{u}} (F : Z ⟶ (ihom X).obj Y) (z : Z _⦋0⦌) :
    lift (𝟙 X) (SSet.const z) ≫ uncurry F =
      (functorVertexEquiv X Y).symm (F.app (Opposite.op ⦋0⦌) z) := by
  let G := (functorVertexEquiv X Y).symm (F.app (Opposite.op ⦋0⦌) z)
  have hv : (SSet.const z : X ⟶ Z) ≫ F = SSet.const (functorVertex G) := by
    rw [SSet.const_comp]
    exact congrArg SSet.const ((functorVertexEquiv X Y).apply_symm_apply _).symm
  calc
    lift (𝟙 X) (SSet.const z) ≫ uncurry F =
        lift (𝟙 X) (𝟙 X) ≫ (X ◁ (SSet.const z : X ⟶ Z)) ≫ uncurry F := by
      rw [← Category.assoc]
      rfl
    _ = lift (𝟙 X) (𝟙 X) ≫ uncurry ((SSet.const z : X ⟶ Z) ≫ F) := by
      rw [uncurry_natural_left]
    _ = lift (𝟙 X) (𝟙 X) ≫ uncurry (SSet.const (functorVertex G)) := by rw [hv]
    _ = G := by
      rw [uncurry_const_functorVertex, ← Category.assoc, lift_fst, Category.id_comp]

end SerrePositivity.InfinityCategories.F2.Ind
