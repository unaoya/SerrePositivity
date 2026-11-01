module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFirstFactorWordActionDiagrams
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.EndpointFunctorHEq

/-!
# 元の切断因子の固定端点関手と語の作用

概要：元の端点表示を移すと prefix・残りの全関手が厳密に一致する。
方針：全図式の異種等式と固定端点の回収を使う。
規約：同じ元の生成矢の端点の等式だけを使う。
使われ方：元の各単体と同じ余極限の標準射の比較。
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
lemma prefix_functor_heq :
    HEq (AttachedPrefix.functor W τ h ⋙ WordAction.functor
      (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)))
    (Attachments.prefixFunctor W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT) :=
  Zigzag.MovingDiagram.fixedFunctor_heq rfl rfl
    (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
      (generator_eq W f τ h hT)).symm _ _ (prefix_diagram W f τ h hT)

include hT in
lemma residual_functor_heq :
    HEq (Attachments.residualFunctor W τ (AttachedPrefix.index W τ h)
      (AttachedPrefix.nonempty W τ h) ⋙ WordAction.functor
        (residualMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)))
    (Attachments.residualFunctor W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT) :=
  Zigzag.MovingDiagram.fixedFunctor_heq rfl
    (congrArg (fun g : Quiver.Total C => (show Paths C from g.right))
      (generator_eq W f τ h hT)).symm rfl _ _ (residual_diagram W f τ h hT)

include hT in
lemma prefix_functor :
    AttachedPrefix.functor W τ h ⋙ WordAction.functor
      (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)) ⋙
      Zigzag.EndpointChange.functor rfl
        (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
          (generator_eq W f τ h hT)).symm =
    Attachments.prefixFunctor W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT :=
  Zigzag.EndpointChange.comp_eq_of_heq rfl _ _ _ (prefix_functor_heq W f τ h hT)

include hT in
lemma residual_functor :
    Attachments.residualFunctor W τ (AttachedPrefix.index W τ h) (AttachedPrefix.nonempty W τ h) ⋙
      WordAction.functor
        (residualMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)) ⋙
      Zigzag.EndpointChange.functor
        (congrArg (fun g : Quiver.Total C => (show Paths C from g.right))
          (generator_eq W f τ h hT)).symm rfl =
    Attachments.residualFunctor W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT :=
  Zigzag.EndpointChange.comp_eq_of_heq _ rfl _ _ (residual_functor_heq W f τ h hT)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
