module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramFixed

/-!
# 定数自然変換からの一列の全関手の回収

概要：元の任意の射の定数自然変換を元の一定 zigzag 関手へ回収する。
方針：全対象と二つの縦成分を照合する。
規約：元の射に長さ・生成性の制限を課さない。
使われ方：恒等列を元の arrowSimplex と標準射へ渡す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  (W : MorphismProperty C) [W.IsMultiplicative] {X Y : C} (p : X ⟶ Y)

lemma constant_diagram_fixedFunctor :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W ((Functor.const D).map p) (fun _ => W.id_mem _)
      (fun _ => W.id_mem _)).fixedFunctor = (Functor.const D).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) p) := by
  refine CategoryTheory.Functor.ext (F := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W ((Functor.const D).map p)
    (fun _ => W.id_mem _) (fun _ => W.id_mem _)).fixedFunctor)
    (G := (Functor.const D).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) p)) (fun _ => rfl) ?_
  intro d e f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
  intro j
  change Fin 2 at j
  cases j using Fin.cases with
  | zero => rfl
  | succ j => rfl

lemma identity_diagram_fixedFunctor (X : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W (𝟙 ((Functor.const D).obj X)) (fun _ => W.id_mem _)
      (fun _ => W.id_mem _)).fixedFunctor =
        (Functor.const D).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (𝟙 X)) := by
  have h := constant_diagram_fixedFunctor (D := D) W (𝟙 X)
  rw [CategoryTheory.Functor.map_id] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
