module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexUliftCategory

/-!
概要：全単体の圏の nerve と底の宇宙持ち上げは、初頂点写像と指定辺を保って可換。
方針：単体の値を上下する関手を射列へ適用し、実際の単体集合の同型を作る。
規約：宇宙持ち上げを同値だけで置き換えず、指定写像の厳密な等式を保持する。
使われ方：共同切断評価と同じ宇宙での局所化。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 持ち上げた底の単体圏の nerve と、元の単体圏の nerve の持ち上げとの同型。 -/
def transportSimplexNerveUliftIso (B : SSet.{u}) :
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory ((SSet.uliftFunctor.{v, u}).obj B)) ≅
      (SSet.uliftFunctor.{v, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) where
  hom := {
    app := fun _ ↦ ↾fun σ ↦ ULift.up (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftDown.{u, v} B)
    naturality := fun {_ _} _ ↦ rfl }
  inv := {
    app := fun _ ↦ ↾fun σ ↦ σ.down ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftUp.{u, v} B
    naturality := fun {_ _} _ ↦ rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro σ
    change (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftDown.{u, v} B) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftUp B = σ
    rw [Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftDown_up, Functor.comp_id]
  inv_hom_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro σ
    apply ULift.ext
    change (σ.down ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftUp.{u, v} B) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftDown B = σ.down
    rw [Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftUp_down, Functor.comp_id]

/-- nerve の宇宙比較は、指定された初頂点写像と厳密に可換。 -/
lemma transportSimplexNerveUliftIso_firstVertex (B : SSet.{u}) :
    (transportSimplexNerveUliftIso.{u, v} B).hom ≫
        (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap ((SSet.uliftFunctor.{v, u}).obj B) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

/-- nerve の宇宙比較の指定辺の像は、元の指定辺を持ち上げた集合そのもの。 -/
lemma transportSimplexNerveUliftIso_initialEdges_image (B : SSet.{u}) :
    (transportSimplexNerveUliftIso.{u, v} B).hom.app (Opposite.op ⦋1⦌) ''
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges ((SSet.uliftFunctor.{v, u}).obj B) =
      ULift.up '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B := by
  apply Set.Subset.antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftDown.{u, v} B,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftDown_initialEdges B σ).mpr hσ, rfl⟩
  · rintro _ ⟨σ, hσ, rfl⟩
    refine ⟨σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftUp.{u, v} B,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftUp_initialEdges B σ).mpr hσ, ?_⟩
    apply ULift.ext
    change (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftUp.{u, v} B) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftDown B = σ
    rw [Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUliftUp_down, Functor.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
