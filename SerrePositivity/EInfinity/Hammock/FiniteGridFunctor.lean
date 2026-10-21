module

public import SerrePositivity.EInfinity.Hammock.FiniteGridMaps

/-!
# 元の有限 hammock grid の関手的な因子化

概要：持ち上げた全行と全縦射は元の関手と同じ恒等・合成を満たす。
方針：元の包含の忠実性と各縦成分の射影式を使う。
規約：射影後は元の全 grid の同じ関手へ厳密に戻る。
使われ方：全被覆の hammock の有限部分木による余極限表示。
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

def functor : letI := FiniteQuiver.quiver S
    I ⥤ Zigzag (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex S))) a
      ((Paths.of (FiniteQuiver.Vertex S)).obj ⟨X, hx⟩)
      ((Paths.of (FiniteQuiver.Vertex S)).obj ⟨Y, hy⟩) := by
  letI := FiniteQuiver.quiver S
  letI := FiniteQuiver.pathInclusion_faithful S
  exact
    { obj i := row S F hx hy hF i
      map f := map S F hx hy hF f
      map_id i := by
        apply Zigzag.hom_ext
        intro j
        apply (FiniteQuiver.pathInclusion S).map_injective
        change (FiniteQuiver.pathInclusion S).map (vertical S F hF (𝟙 i) j) = _
        rw [vertical_projection, Zigzag.id_app, (FiniteQuiver.pathInclusion S).map_id]
        exact congrArg (fun r : F.obj i ⟶ F.obj i => r.app j) (F.map_id i)
      map_comp {i i' i''} f g := by
        apply Zigzag.hom_ext
        intro j
        apply (FiniteQuiver.pathInclusion S).map_injective
        change (FiniteQuiver.pathInclusion S).map (vertical S F hF (f ≫ g) j) =
          (FiniteQuiver.pathInclusion S).map (vertical S F hF f j ≫ vertical S F hF g j)
        rw [vertical_projection, (FiniteQuiver.pathInclusion S).map_comp,
          vertical_projection, vertical_projection]
        exact congrArg (fun r : F.obj i ⟶ F.obj i'' => r.app j) (F.map_comp f g) }

lemma map_projection {i i' : I} (f : i ⟶ i') : letI := FiniteQuiver.quiver S
    HEq (Zigzag.Relative.map (FiniteQuiver.pathRelative S) (map S F hx hy hF f))
      (F.map f) := by
  let := FiniteQuiver.quiver S
  apply Zigzag.hom_hext (row_projection S F hx hy hF i) (row_projection S F hx hy hF i')
  intro j
  exact heq_of_eq (vertical_projection S F hF f j)

lemma functor_projection : letI := FiniteQuiver.quiver S
    functor S F hx hy hF ⋙ Zigzag.Relative.functor (FiniteQuiver.pathRelative S) = F := by
  let := FiniteQuiver.quiver S
  apply CategoryTheory.Functor.hext (fun i => row_projection S F hx hy hF i)
  intro i i' f
  exact map_projection S F hx hy hF f

end SerrePositivity.EInfinity.Hammock.FiniteGrid
