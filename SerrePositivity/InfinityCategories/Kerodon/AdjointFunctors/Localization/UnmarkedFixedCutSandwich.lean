module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCut

/-!
# 固定生成矢での切断の前後への連結と厳密な回収

概要：指定前置射列と任意の後置射列を加えた元の固定切断を構成する。
方針：元の射列の結合則と固定切断の一意性を使う。
規約：同じ元の生成矢と前後の射列を保持する。
使われ方：圧縮後の切断の接頭射・残りを元の切断へ照合する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutSandwich
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a : Quiver.Total C} {X Y X' Y' : C} {p : Quiver.Path X Y} (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a p)
  (u : Quiver.Path X' X) (v : Quiver.Path Y Y') (hu : W.paths u)

def sandwich : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a (u.comp (p.comp v)) where
  left := u.comp P.left
  right := P.right.comp v
  left_mem := W.paths.comp_mem _ _ hu P.left_mem
  unmarked := P.unmarked
  factorization := (congrArg (fun q : Quiver.Path X Y => u.comp (q.comp v))
    P.factorization).trans (by simp only [Quiver.Path.comp_assoc])

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutSandwich (sandwich)


include hu in
lemma sandwich_left (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a (u.comp (p.comp v))) : Q.left = u.comp P.left :=
  congrArg (fun R => R.left) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedCut_ext W Q (sandwich W P u v hu))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutSandwich (sandwich_left)


include hu in
lemma sandwich_right (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a (u.comp (p.comp v))) : Q.right = P.right.comp v :=
  congrArg (fun R => R.right) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedCut_ext W Q (sandwich W P u v hu))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutSandwich (sandwich_right)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutSandwich
