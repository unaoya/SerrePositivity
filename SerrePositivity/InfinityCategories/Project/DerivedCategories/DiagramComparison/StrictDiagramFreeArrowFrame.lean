module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeAtReindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeValueFrameConditions

/-!
概要：同じ自由frameをHom要素圏の反対圏上の図式に束ねる。
方針：始点では元のframeを共変に、終点では評価の左随伴を反変に作用させる。
規約：関手の合成・uncurryを使い、全添字射の作用を持たせる。
使われ方：HTT 4.2.4.4のRR02(a)、実二変数係数の重み付き実現の源。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- Hom要素圏の反対圏から、終点の反対と始点の対への指定関手。 -/
def strictDiagramFreeArrowIndex (d : StrictDiagramDirection) :
    (StrictDiagramArrowElements.{u} d)ᵒᵖ ⥤
      (strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d where
  obj t := (Opposite.op (AsSmall.down.obj t.unop.obj.2),
    AsSmall.down.obj t.unop.obj.1.unop)
  map f := ((AsSmall.down.map f.unop.hom.2).op, AsSmall.down.map f.unop.hom.1.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)

/-- 二つの添字全体にわたる、同じ自由frameの族。 -/
def strictDiagramFreeValueFrameFamily (X : StrictComplexDiagram A d) :
    (strictDiagramIndex d)ᵒᵖ ⥤ strictDiagramIndex d ⥤
      SimplexCategory ⥤ StrictComplexDiagram A d :=
  strictDiagramFreeAtFunctor A d ⋙
    Functor.whiskeringRight SimplexCategory (Complex A) (StrictComplexDiagram A d) ⋙
      (Functor.whiskeringLeft (strictDiagramIndex d) (SimplexCategory ⥤ Complex A)
        (SimplexCategory ⥤ StrictComplexDiagram A d)).obj
          (strictDiagramEvaluatedSourceFrames A d X)

/-- 実際のHom要素圏の反対圏上の自由frame図式。 -/
def strictDiagramFreeArrowFrame (X : StrictComplexDiagram A d) :
    (StrictDiagramArrowElements.{u} d)ᵒᵖ ⥤ SimplexCategory ⥤ StrictComplexDiagram A d :=
  strictDiagramFreeArrowIndex d ⋙ Functor.uncurry.obj (strictDiagramFreeValueFrameFamily A d X)

/-- 全族の各値は、前に指定した同じ自由frameである。 -/
lemma strictDiagramFreeArrowFrame_obj (X : StrictComplexDiagram A d)
    (t : StrictDiagramArrowElements.{u} d) :
    (strictDiagramFreeArrowFrame A d X).obj (Opposite.op t) =
      strictDiagramFreeValueFrame A d X
        (AsSmall.down.obj t.obj.1.unop) (AsSmall.down.obj t.obj.2) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
