module

public import SerrePositivity.EInfinity.Hammock.UnmarkedGeneratorValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagPathIntervalValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorWordPath

/-!
# 元の hammock の非空文字列と非空列の同定

概要：元の非指定文字列が空でないことを、元の列の文字列の非空性で特徴づける。
方針：値の射列の各隣接射を元の列の消去へ照合し、全合成の空性を使う。
規約：元の評価関手・全列・空語・端点移送を保持する。
使われ方：全語の非空部分の余極限と元の hammock の非空部分との同定。
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

lemma edge_column (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i := by
  cases hi : w.direction i with
  | forward =>
    rw [edge_forward W S i hi]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W (eqToHom _ ≫ S.arrow i ≫ eqToHom _) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W (S.arrow i)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_transport W _ _ (S.arrow i)
  | backward => rw [edge_backward W S i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column_backward W S i hi]

lemma path_adjacent_column (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) (i : Fin w.length) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S).map'
      i.val (i.val + 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_map_adjacent (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S i).trans
    (edge_column W S i)

lemma value_path_hom (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) : value W S =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S).hom := by
  unfold value _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.word_eqToHom]
  change ([] ++ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S).hom)
    ++ [] = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.functor W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.inverts W) S).hom
  exact List.append_nil _

lemma value_eq_nil_iff (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) :
    value W S = [] ↔ ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i = [] := by
  rw [value_path_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composable_hom_eq_nil_iff]
  constructor
  · intro h i
    rw [← path_adjacent_column W S i]
    exact h i
  · intro h i
    rw [path_adjacent_column W S i]
    exact h i

lemma value_ne_nil_iff (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) :
    value W S ≠ [] ↔ ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i ≠ [] := by
  classical
  simp only [ne_eq, value_eq_nil_iff, not_forall]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
