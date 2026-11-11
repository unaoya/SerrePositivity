module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverArrowLift

/-!
# 元の支持内の図式の有限 quiver への関手的持ち上げ

概要：全対象と全射列の支持が有限集合内にある元の図式を持ち上げる。
方針：元の一意な liftArrow を各射へ適用し、忠実性で恒等と合成を検査する。
規約：射影後は元の同じ関手へ厳密に戻る。
使われ方：元の hammock grid の有限部分木への因子化。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverFunctorLift
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {I : Type w} [Category.{w'} I]
  (S : Finset Q) (F : I ⥤ Paths Q)
  (hobj : ∀ i, (show Q from F.obj i) ∈ S)
  (hmap : ∀ {i j} (f : i ⟶ j), @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices Q _ _ _ (F.map f) ⊆ S)

def liftObject (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S := ⟨F.obj i, hobj i⟩

def liftMap {i j : I} (f : i ⟶ j) : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (liftObject S F hobj i) ⟶
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (liftObject S F hobj j) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftArrow S (liftObject S F hobj i) (liftObject S F hobj j) (F.map f) (hmap f)

lemma liftMap_projection {i j : I} (f : i ⟶ j) : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map (liftMap S F hobj hmap f) = F.map f := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftArrow_projection S (liftObject S F hobj i) (liftObject S F hobj j)
    (F.map f) (hmap f)

def liftFunctor : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S; I ⥤ Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathInclusion_faithful S
  exact
    { obj i := (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (liftObject S F hobj i)
      map f := liftMap S F hobj hmap f
      map_id i := by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_injective
        rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_id, liftMap_projection]
        exact F.map_id i
      map_comp f g := by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_injective
        rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map_comp, liftMap_projection, liftMap_projection,
          liftMap_projection]
        exact F.map_comp f g }

lemma liftFunctor_projection : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    liftFunctor S F hobj hmap ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S = F := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  refine CategoryTheory.Functor.ext (F := _) (G := F) (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact liftMap_projection S F hobj hmap f

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverFunctorLift
