module
public import SerrePositivity.KST.Fibration.CoherentTriangleDiagonal

/-! # 元の coherent 二単体の短 path と、元の二短辺の実 Hom 頂点の一致 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 第一短辺の同じ両端を持つ path は、元の第一短 path そのもの。 -/
theorem coherentTriangleFirstPath_unique
    (p : Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 1)) :
    p = coherentTriangleFirstPath := by
  apply SimplicialThickening.Path.ext
  ext k
  change k ∈ p.I ↔ k.down ≤ 1
  constructor
  · exact p.le_right k
  · intro hk
    rcases k with ⟨k⟩
    fin_cases k
    · exact p.left
    · exact p.right
    · simp at hk

/-- 第二短辺の同じ両端を持つ path は、元の第二短 path そのもの。 -/
theorem coherentTriangleLastPath_unique
    (p : Path (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) :
    p = coherentTriangleLastPath := by
  apply SimplicialThickening.Path.ext
  ext k
  change k ∈ p.I ↔ 1 ≤ k.down
  constructor
  · exact p.left_le k
  · intro hk
    rcases k with ⟨k⟩
    fin_cases k
    · simp at hk
    · exact p.left
    · exact p.right

/-- 元の第一短 path の像は、同じ第一短辺 δ₂ の実 Hom 頂点である。 -/
theorem coherentTriangleFirst_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    coherentTriangleHomVertex s coherentTriangleFirstPath =
      coherentArrowHomVertex ((SimplicialNerve C).δ 2 s) :=
  congrArg (coherentTriangleHomVertex s)
    (coherentTriangleFirstPath_unique ((SimplicialThickening.functorMap
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).obj
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath)).symm

/-- 元の第二短 path の像は、同じ第二短辺 δ₀ の実 Hom 頂点である。 -/
theorem coherentTriangleLast_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    coherentTriangleHomVertex s coherentTriangleLastPath =
      coherentArrowHomVertex ((SimplicialNerve C).δ 0 s) :=
  congrArg (coherentTriangleHomVertex s)
    (coherentTriangleLastPath_unique ((SimplicialThickening.functorMap
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).obj
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath)).symm

end SerrePositivity.KST.Fibration
