module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows

/-!
# 有限支持に持ち上げた元の hammock grid の全縦射

概要：元の全縦射を持ち上げ、端点の恒等性と全正方形の可換性を回収する。
方針：元の包含の忠実性で元の正方形へ戻して検査する。
規約：全横列・全縦射の内部の生成辺を保持する。
使われ方：元の全 grid の関手的な持ち上げ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {I : Type w} [Category.{w'} I]
  [Fintype I] [∀ i j : I, Fintype (i ⟶ j)] {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths Q}
  (S : Finset Q) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) a X Y)
  (hx : (show Q from X) ∈ S) (hy : (show Q from Y) ∈ S) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F ⊆ S)

def vertical {i i' : I} (f : i ⟶ i') (j : Fin (a.length + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.vertex S F hF i j) ⟶
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.vertex S F hF i' j) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftArrow S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.vertex S F hF i j) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.vertex S F hF i' j)
    ((F.map f).app j) (fun _ hp => hF (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport_vertical F f j hp))

lemma vertical_projection {i i' : I} (f : i ⟶ i') (j : Fin (a.length + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map (vertical S F hF f j) = (F.map f).app j := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftArrow_projection S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.vertex S F hF i j) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.vertex S F hF i' j)
    ((F.map f).app j) _

def map {i i' : I} (f : i ⟶ i') : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.row S F hx hy hF i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.row S F hx hy hF i' := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathInclusion_faithful S
  exact
    { app j := vertical S F hF f j
      app_mem _ := trivial
      first := by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_injective
        rw [vertical_projection, eqToHom_map]
        exact (F.map f).first
      last := by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_injective
        rw [vertical_projection, eqToHom_map]
        exact (F.map f).last
      comm k := by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_injective
        rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_comp, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_comp,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.row_arrow_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.row_arrow_projection, vertical_projection, vertical_projection]
        exact (F.map f).comm k }

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps
