module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteGridRows

/-!
# 有限支持に持ち上げた元の hammock grid の全縦射

概要：元の全縦射を持ち上げ、端点の恒等性と全正方形の可換性を回収する。
方針：元の包含の忠実性で元の正方形へ戻して検査する。
規約：全横列・全縦射の内部の生成辺を保持する。
使われ方：元の全 grid の関手的な持ち上げ。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FiniteGrid
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {I : Type w} [Category.{w'} I]
  [Fintype I] [∀ i j : I, Fintype (i ⟶ j)] {a : Word} {X Y : Paths Q}
  (S : Finset Q) (F : I ⥤ Zigzag (⊤ : MorphismProperty (Paths Q)) a X Y)
  (hx : (show Q from X) ∈ S) (hy : (show Q from Y) ∈ S) (hF : gridPathSupport F ⊆ S)

def vertical {i i' : I} (f : i ⟶ i') (j : Fin (a.length + 1)) :
    letI := FiniteQuiver.quiver S
    (Paths.of (FiniteQuiver.Vertex S)).obj (vertex S F hF i j) ⟶
      (Paths.of (FiniteQuiver.Vertex S)).obj (vertex S F hF i' j) := by
  letI := FiniteQuiver.quiver S
  exact FiniteQuiver.liftArrow S (vertex S F hF i j) (vertex S F hF i' j)
    ((F.map f).app j) (fun _ hp => hF (gridPathSupport_vertical F f j hp))

lemma vertical_projection {i i' : I} (f : i ⟶ i') (j : Fin (a.length + 1)) :
    letI := FiniteQuiver.quiver S
    (FiniteQuiver.pathInclusion S).map (vertical S F hF f j) = (F.map f).app j := by
  let := FiniteQuiver.quiver S
  exact FiniteQuiver.liftArrow_projection S (vertex S F hF i j) (vertex S F hF i' j)
    ((F.map f).app j) _

def map {i i' : I} (f : i ⟶ i') : letI := FiniteQuiver.quiver S
    row S F hx hy hF i ⟶ row S F hx hy hF i' := by
  letI := FiniteQuiver.quiver S
  letI := FiniteQuiver.pathInclusion_faithful S
  exact
    { app j := vertical S F hF f j
      app_mem _ := trivial
      first := by
        apply (FiniteQuiver.pathInclusion S).map_injective
        rw [vertical_projection, eqToHom_map]
        exact (F.map f).first
      last := by
        apply (FiniteQuiver.pathInclusion S).map_injective
        rw [vertical_projection, eqToHom_map]
        exact (F.map f).last
      comm k := by
        apply (FiniteQuiver.pathInclusion S).map_injective
        rw [(FiniteQuiver.pathInclusion S).map_comp, (FiniteQuiver.pathInclusion S).map_comp,
          row_arrow_projection, row_arrow_projection, vertical_projection, vertical_projection]
        exact (F.map f).comm k }

end SerrePositivity.EInfinity.Hammock.FiniteGrid
