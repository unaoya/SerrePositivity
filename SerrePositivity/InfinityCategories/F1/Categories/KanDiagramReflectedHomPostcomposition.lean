module

public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramHomPostcomposition
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeInternalHomEvaluation

/-!
概要：表現可能 Hom 図式の全後合成を反転し、係数の同時評価の厳密な式を与える。
方針：一成分の式と内部 Hom の反転同型の uncurry を使う。
規約：元の全変換のパラメーターを保持する。
使われ方：左切断 prism の終点の係数を実際の weighted 作用へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 全後合成を一成分で評価すると、元の変換の同じ成分への後合成そのもの。 -/
lemma kanDiagramHomPostcomposition_component {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) (i : I) :
    kanDiagramHomPostcomposition F G x ≫ strictDiagramMappingComponent
      (simplicialHomDiagram F.val x) (simplicialHomDiagram G.val x) i =
    strictDiagramMappingComponent (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i ≫
      kanDiagramHomPostcompositionComponent F G x i := rfl

/-- 表現可能 Hom 図式の後合成を、反転した係数図式間の全変換へ移す。 -/
def kanDiagramReflectedHomPostcomposition {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) :
    (SimplicialCategory.sHom F G).op ⟶
      strictDiagramMappingSpace (simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
        (simplicialHomDiagram G.val x ⋙ SSet.opFunctor) :=
  SSet.opFunctor.map (kanDiagramHomPostcomposition F G x) ≫
    strictDiagramOppositeHom (simplicialHomDiagram F.val x) (simplicialHomDiagram G.val x)

/-- 反転した後合成の一成分は、元の後合成の成分と同じ反転内部 Hom の同型の合成。 -/
lemma kanDiagramReflectedHomPostcomposition_component {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) (i : I) :
    kanDiagramReflectedHomPostcomposition F G x ≫ strictDiagramMappingComponent
      (simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
      (simplicialHomDiagram G.val x ⋙ SSet.opFunctor) i =
    SSet.opFunctor.map (strictDiagramMappingComponent
      (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i) ≫
      SSet.opFunctor.map (kanDiagramHomPostcompositionComponent F G x i) ≫
        (oppositeInternalHomIso (SimplicialCategory.sHom x (F.val.obj i))
          (SimplicialCategory.sHom x (G.val.obj i))).hom := by
  rw [kanDiagramReflectedHomPostcomposition, Category.assoc,
    strictDiagramOppositeHom_component, ← Category.assoc, ← SSet.opFunctor.map_comp,
    kanDiagramHomPostcomposition_component, SSet.opFunctor.map_comp, Category.assoc]
  rfl

/-- 反転した全後合成の実際の評価は、元の二係数を反転側で豊穣合成する同じ射。 -/
lemma kanDiagramReflectedHomPostcomposition_uncurry {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) (i : I) :
    uncurry (kanDiagramReflectedHomPostcomposition F G x ≫ strictDiagramMappingComponent
      (simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
      (simplicialHomDiagram G.val x ⋙ SSet.opFunctor) i) =
    ((SimplicialCategory.sHom x (F.val.obj i)).op ◁ SSet.opFunctor.map
      (strictDiagramMappingComponent (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i)) ≫
      (opTensorIso (SimplicialCategory.sHom x (F.val.obj i))
        (SimplicialCategory.sHom (F.val.obj i) (G.val.obj i))).hom ≫
      SSet.opFunctor.map (eComp SSet x (F.val.obj i) (G.val.obj i)) := by
  rw [kanDiagramReflectedHomPostcomposition_component, ← Category.assoc,
    ← SSet.opFunctor.map_comp, oppositeInternalHom_map_uncurry,
    uncurry_natural_left, kanDiagramHomPostcompositionComponent, uncurry_curry,
    SSet.opFunctor.map_comp]
  rfl

end SerrePositivity.InfinityCategories
