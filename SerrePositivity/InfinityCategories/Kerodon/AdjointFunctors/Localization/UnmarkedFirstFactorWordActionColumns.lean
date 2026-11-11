module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedPrefixWordActionInner
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedResidualWordActionInner
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedPrefixWordActionOuter
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedResidualWordActionOuter

/-!
# 元の最小列で切断した因子の全横列と語の作用

概要：内部接続列と外側の全列を合わせ、元の因子の全横列を回収する。
方針：連結語の列の左右の場合分けを使う。
規約：元の全行・全方向・同じ切断端点を保持する。
使われ方：全因子図式と同じ hammock 余極限の標準射の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n) (h : ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])
  (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).obj 0)
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) ≠ []) (d : Fin (n.unop.len + 1))

include hT in
lemma prefix_columns (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.diagram W τ h).obj d)).arrow k)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
        (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT).obj d).arrow k) := by
  cases k using Fin.addCases with
  | left k =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_outer_arrow W f τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h) hT d k
  | right k =>
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_inner_action_arrow W f τ h hT d

include hT in
lemma residual_columns (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d)).arrow k)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
        (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT).obj d).arrow k) := by
  cases k using Fin.addCases with
  | left k =>
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_inner_action_arrow W f τ h hT d
  | right k =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_outer_arrow W f τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h) hT d k

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
