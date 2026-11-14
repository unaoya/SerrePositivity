module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeRealizationProjective

/-!
概要：元の半自由strict図式の台の一点加群図式を、全射を持つ通常関手にする。
方針：既存の一点定数関手と台の充満包含を図式圏で後合成する。
規約：対象ごとの選択を使わず、元の同じ射を保つ。
使われ方：3b-3 R6 U26〜U28、同じ全native余錐族への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U26：既存の一点定数関手と包含の、図式圏の全通常関手。 -/
def strictSemifreePointUnderlyingFunctor :
    StrictSemifreeDiagram A SimplexCategoryᵒᵖ ⥤
      (SimplexCategoryᵒᵖ ⥤ ModuleCategory A PUnit.{1}) :=
  (Functor.whiskeringRight _ _ _).obj
    ((semifreePointConstant A).onClosed ⋙
      (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
        (dgModuleSemifreeProperty A PUnit.{1})).onClosed)

/-- U27：対象は既存の同じ一点半自由図式の台である。 -/
lemma strictSemifreePointUnderlyingFunctor_obj
    (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    (strictSemifreePointUnderlyingFunctor A).obj F =
      pointSemifreeUnderlyingDiagram A (strictSemifreePointDiagram A F) := rfl

/-- U28：各値の射影性は既存の半自由性から供給する。 -/
lemma strictSemifreePointUnderlyingFunctor_projective
    (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) (j : SimplexCategoryᵒᵖ) :
    moduleHomotopicallyProjective A PUnit.{1}
      (((strictSemifreePointUnderlyingFunctor A).obj F).obj j) :=
  pointSemifreeUnderlyingDiagram_projective A (strictSemifreePointDiagram A F) j

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
