module

public import SerrePositivity.EInfinity.Hammock.RelativeCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor

/-!
# 固定した端点の表示を保つ hammock 余極限写像

概要：端点の等式の移送を元の余極限写像へ合成し、合成の保存を得る。
方針：元の全語の係数写像と端点表示の等式を使う。
規約：元の全語の図式・標準射・合成を保持する。
使われ方：自由 hammock の全単体作用素に自然な合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.Relative
open CategoryTheory CategoryTheory.Limits
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {X Y Z : C} {X' Y' Z' : D}

def fixedGraphDiagramMap (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram V X' Y' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap F X Y ≫ eqToHom (congrArg₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram V) hX hY)

lemma fixedGraphDiagramMap_app (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : (fixedGraphDiagramMap F hX hY).app w =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := w) F hX hY) := by
  cases hX
  cases hY
  rfl

def fixedColimitMap (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph V X' Y' :=
  colim.map (fixedGraphDiagramMap F hX hY)

lemma fixedColimitMap_inclusion (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ fixedColimitMap F hX hY =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := w) F hX hY) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V X' Y' w := by
  exact (colimit.ι_map (fixedGraphDiagramMap F hX hY) w).trans
    (congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V X' Y' w) (fixedGraphDiagramMap_app F hX hY w))

lemma fixedColimitMap_composePoint
    (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y') (hZ : F.functor.obj Z = Z')
    {n : SimplexCategoryᵒᵖ} (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).obj n)
    (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z).obj n) :
    (fixedColimitMap F hX hZ).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint V X' Y' Z' ((fixedColimitMap F hX hY).app n p)
        ((fixedColimitMap F hY hZ).app n q) := by
  cases hX
  cases hY
  cases hZ
  simpa only [fixedColimitMap, fixedGraphDiagramMap, eqToHom_refl,
    Category.comp_id, colimitMap] using composePoint_map F p q

end SerrePositivity.EInfinity.Hammock.Relative
