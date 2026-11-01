module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFirstFactorWordActionColumns
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagEndpointHExt

/-!
# 元の切断因子の全図式と制限した語の作用

概要：元の prefix・残りの全図式を制限射の作用と異種等式で同定する。
方針：元の端点・全頂点・全横列・全縦射の回収を外延性で合成する。
規約：同じ生成矢の表示の等式だけを使い、局所化後の同型で置き換えない。
使われ方：同じ元の hammock 余極限への標準射の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n) (h : ∃ i, column W (τ.obj 0) i ≠ [])
  (hT : column W ((τ ⋙ WordAction.functor f).obj 0)
    (f.orderHom (AttachedPrefix.index W τ h)) ≠ [])

include hT in
lemma prefix_diagram :
    HEq (Zigzag.MovingDiagram.wordAction
      (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h))
      (AttachedPrefix.diagram W τ h))
    (Attachments.prefixDiagram W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT) := by
  have hY := (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
    (generator_eq W f τ h hT)).symm
  exact Zigzag.MovingDiagram.hext_endpoints rfl
    (congrArg (fun Z : Paths C => (Functor.const (Fin (n.unop.len + 1))).obj Z) hY) _ _
    (fun d => Zigzag.object_hext_endpoints rfl hY _ _ (prefix_vertices W f τ h hT d)
      (prefix_columns W f τ h hT d)) (fun g k => prefix_apps W f τ h hT g k)

include hT in
lemma residual_diagram :
    HEq (Zigzag.MovingDiagram.wordAction
      (residualMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h))
      (Attachments.residualDiagram W τ (AttachedPrefix.index W τ h)
        (AttachedPrefix.nonempty W τ h)))
    (Attachments.residualDiagram W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT) := by
  have hX := (congrArg (fun g : Quiver.Total C => (show Paths C from g.right))
    (generator_eq W f τ h hT)).symm
  exact Zigzag.MovingDiagram.hext_endpoints
    (congrArg (fun Z : Paths C => (Functor.const (Fin (n.unop.len + 1))).obj Z) hX) rfl _ _
    (fun d => Zigzag.object_hext_endpoints hX rfl _ _ (residual_vertices W f τ h hT d)
      (residual_columns W f τ h hT d)) (fun g k => residual_apps W f τ h hT g k)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
