module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFactorWordActionColumns
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointHExt

/-!
# 元の切断因子の全図式と制限した語の作用

概要：元の prefix・残りの全図式を制限射の作用と異種等式で同定する。
方針：元の端点・全頂点・全横列・全縦射の回収を外延性で合成する。
規約：同じ生成矢の表示の等式だけを使い、局所化後の同型で置き換えない。
使われ方：同じ元の hammock 余極限への標準射の比較。

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
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) ≠ [])

include hT in
lemma prefix_diagram :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.diagram W τ h))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
      (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT) := by
  have hY := (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_eq W f τ h hT)).symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.hext_endpoints rfl
    (congrArg (fun Z : Paths C => (Functor.const (Fin (n.unop.len + 1))).obj Z) hY) _ _
    (fun d => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.object_hext_endpoints rfl hY _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_vertices W f τ h hT d)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_columns W f τ h hT d)) (fun g k => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_apps W f τ h hT g k)

include hT in
lemma residual_diagram :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
      (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT) := by
  have hX := (congrArg (fun g : Quiver.Total C => (show Paths C from g.right))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_eq W f τ h hT)).symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.hext_endpoints
    (congrArg (fun Z : Paths C => (Functor.const (Fin (n.unop.len + 1))).obj Z) hX) rfl _ _
    (fun d => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.object_hext_endpoints hX rfl _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_vertices W f τ h hT d)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_columns W f τ h hT d)) (fun g k => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_apps W f τ h hT g k)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
