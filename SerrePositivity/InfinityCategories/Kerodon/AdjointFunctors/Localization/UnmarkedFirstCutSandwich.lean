module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCut

/-!
# 指定前置射列と任意の後置射列による元の最初の切断

概要：指定された前置射列と任意の後置射列を加えても最初の非指定生成矢を保持する。
方針：元の切断の前後の射列を連結し、切断の一意性を適用する。
規約：後置射列に指定性を仮定しない。
使われ方：語の一つの forward fiber の最初の非指定生成矢の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCutSandwich
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {X Y X' Y' : C} {p : Quiver.Path X Y} (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W p)
  (u : Quiver.Path X' X) (v : Quiver.Path Y Y') (hu : W.paths u)

def sandwich : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W (u.comp (p.comp v)) where
  source := P.source
  target := P.target
  arrow := P.arrow
  left := u.comp P.left
  right := P.right.comp v
  left_mem := W.paths.comp_mem _ _ hu P.left_mem
  unmarked := P.unmarked
  factorization := (congrArg (fun q : Quiver.Path X Y => u.comp (q.comp v))
    P.factorization).trans (by simp only [Quiver.Path.comp_assoc])

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCutSandwich (sandwich)


lemma sandwich_generator :
    (show Quiver.Total C from ⟨(sandwich W P u v hu).source,
      (sandwich W P u v hu).target, (sandwich W P u v hu).arrow⟩) =
      ⟨P.source, P.target, P.arrow⟩ := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCutSandwich (sandwich_generator)


include hu in
lemma generator_of_sandwich (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W (u.comp (p.comp v))) :
    (show Quiver.Total C from ⟨Q.source, Q.target, Q.arrow⟩) =
      ⟨P.source, P.target, P.arrow⟩ :=
  congrArg (fun R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W (u.comp (p.comp v)) =>
    (⟨R.source, R.target, R.arrow⟩ : Quiver.Total C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstCut_ext W Q (sandwich W P u v hu))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCutSandwich (generator_of_sandwich)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCutSandwich
