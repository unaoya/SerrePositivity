module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Path

/-! # 元の coherent 二単体の全長 Hom と、同じ実 path の合成値 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の通常合成の頂点表示は、同じ元の豊穣合成の頂点値である。 -/
theorem simplicialHomVertex_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SimplicialCategory.homEquiv' X Z (f ≫ g) =
      (eComp SSet X Y Z).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' X Y f, SimplicialCategory.homEquiv' Y Z g) :=
  congrArg (SSet.unitHomEquiv _) (eHomEquiv_comp SSet f g)

/-- 指定した元の二単体の、同じ端点間の全 path に対する豊穣 Hom の実作用。 -/
def coherentTriangleLongHom (s : (SimplicialNerve C) _⦋2⦌) :
    nerve (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
      (s.obj ⟨ULift.up 0⟩ ⟶[SSet.{u}] s.obj ⟨ULift.up 2⟩) :=
  s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩

/-- 元の二単体の同じ path の頂点値。 -/
def coherentTriangleHomVertex (s : (SimplicialNerve C) _⦋2⦌)
    {i j : ULift.{u} (Fin 3)} (p : Path i j) :
    (s.obj ⟨i⟩ ⟶[SSet.{u}] s.obj ⟨j⟩) _⦋0⦌ :=
  (s.map ⟨i⟩ ⟨j⟩).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ p)

/-- 元の合成 path の値は、同じ二つの元の頂点値の豊穣合成である。 -/
theorem coherentTriangleHomVertex_comp (s : (SimplicialNerve C) _⦋2⦌)
    {i j k : ULift.{u} (Fin 3)} (p : Path i j) (q : Path j k) :
    coherentTriangleHomVertex s (show (⟨i⟩ : SimplicialThickening _) ⟶ ⟨k⟩ from p ≫ q) =
      (eComp SSet (s.obj ⟨i⟩) (s.obj ⟨j⟩) (s.obj ⟨k⟩)).app (Opposite.op ⦋0⦌)
        (coherentTriangleHomVertex s p, coherentTriangleHomVertex s q) := by
  exact congrArg (fun f => f.app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ p, ComposableArrows.mk₀ q)) (s.map_comp ⟨i⟩ ⟨j⟩ ⟨k⟩)

end SerrePositivity.KST.Fibration
