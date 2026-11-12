module
public import SerrePositivity.KST.SConstruction.CoherentTriangleMappingEdge

/-! # 元の三頂点 Path の値は元の二辺の合成
概要：三角形の中間点を通る元の Path の値を、元の二辺の通常の合成へ同定する。
方針：三頂点区間の Path の所属を比較し、元の豊穣合成則を零単体で用いる。
規約：元の三角形・辺を保持し、局所 Kan 性を使わない。
使われ方：上下の短い因子分解列の定数値を元の二合成へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 三頂点区間で中間点を通る Path は、元の二つの端点 Path の合成そのもの。 -/
lemma coherentTrianglePath_eq_composite
    (p : Path (ULift.up 0 : ULift.{u} (Fin 3)) (ULift.up 2))
    (hp : (ULift.up 1 : ULift.{u} (Fin 3)) ∈ p.I) :
    p = coherentEndpointPathComposite
      (show (ULift.up 0 : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)
      (show (ULift.up 1 : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide) := by
  apply SimplicialThickening.Path.ext
  ext x
  obtain ⟨x⟩ := x
  fin_cases x <;>
    simp [coherentEndpointPathComposite, coherentEndpointPath, p.left, p.right, hp]

/-- 元の三角形の三頂点 Path の値は、同じ二辺の通常の合成の頂点。 -/
lemma coherentTrianglePath_composite_value
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌)
    (p : Path (ULift.up 0 : ULift.{u} (Fin 3)) (ULift.up 2))
    (hp : (ULift.up 1 : ULift.{u} (Fin 3)) ∈ p.I) :
    (s.map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p) =
      SimplicialCategory.homEquiv' _ _
        (coherentSimplexArrow s 0 1 (by decide) ≫ coherentSimplexArrow s 1 2 (by decide)) := by
  rw [coherentTrianglePath_eq_composite p hp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp]
  simp only [coherentSimplexArrow, Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (s.map_comp (.mk (ULift.up 0)) (.mk (ULift.up 1))
      (.mk (ULift.up 2))) (Opposite.op ⦋0⦌))
    (show ((SimplicialCategory.sHom (.mk (ULift.up 0) : SimplicialThickening (ULift.{u} (Fin 3)))
      (.mk (ULift.up 1))) ⊗ SimplicialCategory.sHom
        (.mk (ULift.up 1) : SimplicialThickening (ULift.{u} (Fin 3))) (.mk (ULift.up 2))).obj
      (Opposite.op ⦋0⦌) from
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentEndpointPath (show (ULift.up 0 : ULift.{u} (Fin 3)) ≤
          ULift.up 1 from by decide)),
         _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentEndpointPath (show (ULift.up 1 : ULift.{u} (Fin 3)) ≤
          ULift.up 2 from by decide))))

/-- 三辺を保持する元の実三角形では、三頂点 Path は指定した二辺の合成を回収する。 -/
lemma coherentTrianglePath_specified_composite_heq
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h))
    (p : Path (ULift.up 0 : ULift.{u} (Fin 3)) (ULift.up 2))
    (hp : (ULift.up 1 : ULift.{u} (Fin 3)) ∈ p.I) :
    HEq ((T.simplex.map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p)) (SimplicialCategory.homEquiv' _ _ (f ≫ g)) := by
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
  have hv := coherentTrianglePath_composite_value s p hp
  rw [hf, hg] at hv
  exact hv.heq

/-- 元の三角形の表示を変えても、同じ元の三頂点 Path の値は依存等号で一致する。 -/
lemma coherentTrianglePath_value_heq
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {s t : (SimplicialNerve C) _⦋2⦌} (h : s = t)
    (p : Path (ULift.up 0 : ULift.{u} (Fin 3)) (ULift.up 2)) :
    HEq ((s.map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p))
      ((t.map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p)) := by
  cases h
  rfl

end SerrePositivity.KST.SConstruction
