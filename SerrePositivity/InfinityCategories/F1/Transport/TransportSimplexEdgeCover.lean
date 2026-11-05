module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertexNaturality

/-! # 初頂点写像による元の全辺の厳密な被覆 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- 元の辺からその終点への制限は、初頂点写像で元の同じ辺を回収する。 -/
theorem transportSimplexFirstVertexMap_lastFace_edge {B : SSet.{u}} (s : B _⦋1⦌) :
    (transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (transportSimplexRestriction (SimplexCategory.δ (0 : Fin 2)) s)).edge = s := by
  have hc : transportSimplexFirstVertexMorphism (ComposableArrows.mk₁
      (transportSimplexRestriction (SimplexCategory.δ (0 : Fin 2)) s)) = 𝟙 ⦋1⦌ := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    fin_cases k <;> rfl
  change B.map (transportSimplexFirstVertexMorphism (ComposableArrows.mk₁
    (transportSimplexRestriction (SimplexCategory.δ (0 : Fin 2)) s))).op s = s
  rw [hc, op_id]
  exact Functor.map_id_apply B _ s

/-- 元の全辺は、同じ単体圏の実際の射の初頂点像として厳密に持ち上がる。 -/
theorem transportSimplexFirstVertexMap_edge_surjective (B : SSet.{u}) :
    Function.Surjective ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌)) := by
  intro s
  exact ⟨(nerve.edgeMk (transportSimplexRestriction (SimplexCategory.δ (0 : Fin 2)) s)).edge,
    _root_.SerrePositivity.InfinityCategories.F1.Transport.transportSimplexFirstVertexMap_lastFace_edge s⟩

/-- 初頂点写像の元の指定辺の全逆像は、その像が元の指定辺集合に厳密に一致する。 -/
theorem transportSimplexFirstVertexMap_edge_preimage_image (B : SSet.{u})
    (W : Set (B _⦋1⦌)) :
    (transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌) ''
      ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌) ⁻¹' W) = W :=
  Set.image_preimage_eq W (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportSimplexFirstVertexMap_edge_surjective B)

/-- 宇宙を揃えた初頂点写像でも、指定辺の同じ逆像と像の等式を保持する。 -/
theorem transportSimplexFirstVertexMap_ulift_edge_image (B : SSet.{u})
    (W : Set (B _⦋1⦌)) :
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B)).app
        (Opposite.op ⦋1⦌) ''
      (ULift.up '' ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌) ⁻¹' W)) =
        ULift.up '' W := by
  ext a
  constructor
  · rintro ⟨t, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨_, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportSimplexFirstVertexMap_edge_surjective B s
    refine ⟨ULift.up t, ⟨t, ?_, rfl⟩, congrArg ULift.up ht⟩
    change (transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌) t ∈ W
    rw [ht]
    exact hs

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportSimplexFirstVertexMap_edge_preimage_image := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportSimplexFirstVertexMap_edge_preimage_image

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportSimplexFirstVertexMap_edge_surjective := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportSimplexFirstVertexMap_edge_surjective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportSimplexFirstVertexMap_lastFace_edge := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportSimplexFirstVertexMap_lastFace_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportSimplexFirstVertexMap_ulift_edge_image := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportSimplexFirstVertexMap_ulift_edge_image
