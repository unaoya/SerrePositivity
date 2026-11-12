module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns
public import SerrePositivity.EInfinity.Hammock.HammockValue

/-!
# 元の全語の hammock の非指定生成文字列への評価

概要：全縦射・全語の合成と恒等列の挿入に不変な非指定文字列を元の余極限から得る。
方針：指定射列を恒等射へ送る元の関手を、既存の zigzag の評価へ代入する。
規約：全語・元の標準射・reduced 正規化・augmentation への回収式を保持する。
使われ方：hammock の元の自由積分解の添字。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C}

def value (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) : List (Quiver.Total C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S

lemma value_hom {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y} (f : S ⟶ T) : value W S = value W T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) f

lemma value_wordAction {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X Y) :
    value W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) = value W S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) f S

def graphValue : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (List (Quiver.Total C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph.graphMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W)

def colimitValue (X Y : Paths C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (List (Quiver.Total C)) :=
  Zigzag.Value.colimitValue (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) X Y

lemma graphInclusion_colimitValue (X Y : Paths C) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y w ≫ colimitValue W X Y = graphValue W :=
  Zigzag.Value.graphInclusion_colimitValue (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) X Y w

def reducedValue (X Y : Paths C) : reducedSimplicialSet W.paths X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (List (Quiver.Total C)) :=
  Zigzag.Value.reducedValue (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) X Y

lemma graphNormalization_reducedValue (X Y : Paths C) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    graphNormalization W.paths X Y w ≫ reducedValue W X Y = graphValue W :=
  Zigzag.Value.graphNormalization_reducedValue (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) X Y w

lemma colimitNormalization_reducedValue (X Y : Paths C) :
    colimitNormalization W.paths X Y ≫ reducedValue W X Y = colimitValue W X Y :=
  Zigzag.Value.colimitNormalization_reducedValue (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) X Y

lemma edge_forward (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) (i : Fin w.length)
    (hi : w.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S i hi) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S i hi

lemma edge_backward (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) (i : Fin w.length)
    (hi : w.direction i = .backward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S i = [] := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S i hi]
  have hm : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S i hi).hom = [] :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_marked W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow_allowed .backward S i hi)
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S i hi).hom_inv_id
  change _ ++ _ = ([] : List (Quiver.Total C)) at he
  rw [hm, List.nil_append] at he
  exact he

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
