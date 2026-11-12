module
public import SerrePositivity.KST.Fibration.CoherentTrianglePaths

/-! # 指定 coherent 二単体の直接 path と、元の共有対角の長 Hom の頂点 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 対角面 δ₁ によって、元の一辺の同じ path を二単体へ入れた直接 path。 -/
def coherentTriangleDirectPath :
    Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) :=
  (SimplicialThickening.functorMap (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap
    ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath

/-- 直接 path から任意の元の長 path への実包含射。 -/
def coherentTriangleDirectToPath
    (p : Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) :
    coherentTriangleDirectPath ⟶ p := by
  refine ⟨⟨⟨?_⟩⟩⟩
  rintro k ⟨l, _hl, rfl⟩
  rcases l with ⟨l⟩
  fin_cases l
  · exact p.left
  · exact p.right

/-- 元の一単体から読み出す同じ豊穣 Hom の実頂点。 -/
def coherentArrowHomVertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (a : (SimplicialNerve C) _⦋1⦌) :
    (a.obj ⟨ULift.up 0⟩ ⟶[SSet.{u}] a.obj ⟨ULift.up 1⟩) _⦋0⦌ :=
  (a.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath)

/-- 指定した二単体の直接 path の像は、元の対角面 δ₁ の同じ実 Hom 頂点である。 -/
theorem coherentTriangleDirect_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    coherentTriangleHomVertex s coherentTriangleDirectPath =
      coherentArrowHomVertex ((SimplicialNerve C).δ 1 s) := rfl

end SerrePositivity.KST.Fibration
