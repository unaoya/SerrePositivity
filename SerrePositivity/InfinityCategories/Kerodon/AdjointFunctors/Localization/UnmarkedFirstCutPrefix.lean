module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCutSandwich

/-!
# 非指定文字列の接頭列と元の最初の生成矢

概要：非空の元の非指定文字列を接頭列に持つ射列は、同じ最初の生成矢を持つ。
方針：元の切断の消去式の先頭の Total 矢を比較する。
規約：始域・終域・元の生成射そのものを保持する。
使われ方：語の圧縮前後の最初の非指定生成矢の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {X Y X' Y' : C} {p : Quiver.Path X Y} {q : Quiver.Path X' Y'}

lemma firstCut_generator_of_erasure_prefix (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W p) (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W q)
    (tail : List (Quiver.Total C)) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W p = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W q ++ tail) :
    (⟨P.source, P.target, P.arrow⟩ : Quiver.Total C) = ⟨Q.source, Q.target, Q.arrow⟩ := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstCut_erasure W P, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstCut_erasure W Q, List.cons_append] at h
  exact (List.cons.inj h).1

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
