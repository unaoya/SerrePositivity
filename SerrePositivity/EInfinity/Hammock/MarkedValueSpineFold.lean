module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineGenerators

/-!
# 元の指定値の因子列から任意の圏への評価

概要：指定自由 groupoid の関手と非指定生成矢の像を元の列の順序で合成する。
方針：元の nil/cons 表示で再帰し、元の groupoid の関手の合成則を使う。
規約：元の全端点・指定値・非指定生成矢を保持する。
使われ方：値の因子列の圏の通常の局所化の普遍性。
-/

@[expose] public section
universe u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [Category.{vD} D]
  (K : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ⥤ D)
  (a : ∀ g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W,
    K.obj ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).obj g.val.left) ⟶
      K.obj ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).obj g.val.right))

namespace ValueSpine

def fold {X Y : Paths C} : ValueSpine W Y X →
    (K.obj ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).obj X) ⟶
      K.obj ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).obj Y))
  | .nil _ p => K.map p
  | .cons _ g p t => K.map p ≫ a g ≫ fold t

lemma fold_precompose {X U Y : Paths C} (p : valueHomType W X U) (t : ValueSpine W Y U) :
    fold K a (precompose p t) = K.map p ≫ fold K a t := by
  cases t <;> simp only [fold, precompose, K.map_comp, Category.assoc]

lemma fold_compose {X Y Z : Paths C} (t : ValueSpine W Y X) (s : ValueSpine W Z Y) :
    fold K a (compose t s) = fold K a t ≫ fold K a s := by
  induction t with
  | nil X p => exact fold_precompose K a p s
  | cons X g p t ih => simp only [compose, fold, ih, Category.assoc]

lemma fold_generator (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) : fold K a (generator W g) = a g := by
  change K.map (𝟙 _) ≫ a g ≫ K.map (𝟙 _) = a g
  rw [K.map_id, K.map_id, Category.id_comp, Category.comp_id]

end ValueSpine

variable (W)

def valueFoldFunctor : letI := valueCategory W
    ValueObjects C ⥤ D := by
  letI := valueCategory W
  exact
    { obj X := K.obj ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).obj X)
      map t := ValueSpine.fold K a t
      map_id X := K.map_id _
      map_comp t s := ValueSpine.fold_compose K a t s }

lemma valueFoldFunctor_marked : letI := valueCategory W
    valueMarkedFunctor W ⋙ valueFoldFunctor W K a = K := by
  let := valueCategory W
  exact CategoryTheory.Functor.ext (F := valueMarkedFunctor W ⋙ valueFoldFunctor W K a)
    (G := K) (fun _ => rfl)

lemma valueFoldFunctor_generator (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) : letI := valueCategory W
    (valueFoldFunctor W K a).map (ValueSpine.generator W g) = a g :=
  ValueSpine.fold_generator K a g

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
