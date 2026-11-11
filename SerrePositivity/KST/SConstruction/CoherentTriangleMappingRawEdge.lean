module
public import SerrePositivity.KST.SConstruction.CoherentTriangleMappingEdge

/-! # 指定三角形の復号辺は元の Path 包含辺の評価
概要：指定した三辺に合わせた復号辺から対象と辺の表示変更を消去し、元の豊穣作用へ戻す。
方針：元の三角形の各頂点と辺の等式で移送を消去し、同じ元の辺を回収する。
規約：局所 Kan 性を使わず、復号辺を選び直さない。
使われ方：元の K の二円柱の指定頂点を既存 BF 境界の二脚へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 三辺を指定して復号した実辺は、元の三角形の同じ Path 包含辺の値である。 -/
lemma coherentTriangleMappingEdge_raw_heq
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h)) :
    HEq (coherentTriangleMappingEdge f g h T).edge
      ((T.simplex.map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk (coherentEndpointPathToComposite
          (show (ULift.up 0 : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)
          (show (ULift.up 1 : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide))).edge) := by
  rcases T with ⟨s, h₂, h₀, h₁⟩
  have hx : s.obj (.mk (ULift.up 0)) = X :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).1) h₂
  have hy : s.obj (.mk (ULift.up 1)) = Y :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).2.1) h₂
  have hz : s.obj (.mk (ULift.up 2)) = Z :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).2.1) h₀
  subst X
  subst Y
  subst Z
  have hf : coherentSimplexArrow s 0 1 (by decide) = f :=
    coherentSimplexArrow_of_edge_face s (SimplexCategory.δ (2 : Fin 3)) f h₂
  have hg : coherentSimplexArrow s 1 2 (by decide) = g :=
    coherentSimplexArrow_of_edge_face s (SimplexCategory.δ (0 : Fin 3)) g h₀
  have hh : coherentSimplexArrow s 0 2 (by decide) = h :=
    coherentSimplexArrow_of_edge_face s (SimplexCategory.δ (1 : Fin 3)) h h₁
  subst f
  subst g
  subst h
  rfl

/-- 元の三角形の表示を変えても、同じ Path の包含辺の評価は依存等号で一致する。 -/
lemma coherentTriangleEdgeValue_heq
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {s t : (SimplicialNerve C) _⦋2⦌} (h : s = t)
    (P : (nerve (Path (ULift.up 0 : ULift.{u} (Fin 3)) (ULift.up 2))) _⦋1⦌) :
    HEq ((s.map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋1⦌) P)
      ((t.map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋1⦌) P) := by
  cases h
  rfl

end SerrePositivity.KST.SConstruction
