module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps

/-!
# 元の有限 hammock grid の関手的な因子化

概要：持ち上げた全行と全縦射は元の関手と同じ恒等・合成を満たす。
方針：元の包含の忠実性と各縦成分の射影式を使う。
規約：射影後は元の全 grid の同じ関手へ厳密に戻る。
使われ方：全被覆の hammock の有限部分木による余極限表示。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridFunctor
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {I : Type w} [Category.{w'} I]
  [Fintype I] [∀ i j : I, Fintype (i ⟶ j)] {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths Q}
  (S : Finset Q) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) a X Y)
  (hx : (show Q from X) ∈ S) (hy : (show Q from Y) ∈ S) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F ⊆ S)

def functor : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S))) a
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj ⟨X, hx⟩)
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj ⟨Y, hy⟩) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathInclusion_faithful S
  exact
    { obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.row S F hx hy hF i
      map f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.map S F hx hy hF f
      map_id i := by
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
        intro j
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_injective
        change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.vertical S F hF (𝟙 i) j) = _
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.vertical_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.id_app, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_id]
        exact congrArg (fun r : F.obj i ⟶ F.obj i => r.app j) (F.map_id i)
      map_comp {i i' i''} f g := by
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
        intro j
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_injective
        change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.vertical S F hF (f ≫ g) j) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.vertical S F hF f j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.vertical S F hF g j)
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.vertical_projection, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_comp,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.vertical_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.vertical_projection]
        exact congrArg (fun r : F.obj i ⟶ F.obj i'' => r.app j) (F.map_comp f g) }

lemma map_projection {i i' : I} (f : i ⟶ i') : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathRelative S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.map S F hx hy hF f))
      (F.map f) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.row_projection S F hx hy hF i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.row_projection S F hx hy hF i')
  intro j
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridMaps.vertical_projection S F hF f j)

lemma functor_projection : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    functor S F hx hy hF ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathRelative S) = F := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  apply CategoryTheory.Functor.hext (fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows.row_projection S F hx hy hF i)
  intro i i' f
  exact map_projection S F hx hy hF f

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridFunctor
