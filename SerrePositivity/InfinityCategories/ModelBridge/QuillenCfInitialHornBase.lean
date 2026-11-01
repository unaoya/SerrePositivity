module

public import SerrePositivity.InfinityCategories.ModelBridge.QuillenCfFinalHornBase
public import SerrePositivity.InfinityCategories.ModelBridge.QuillenCfCollageProjection

/-!
概要：元の固定混合初期辺と相対ホーンの底から、全後半頂点の上段性を導く。
方針：頂点一で底の値を固定し、標準区間の単調性を使う。
規約：元の上段 cf 対象を回収する。使われ方：左 Quillen 辺の前合成条件への代入。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open CategoryTheory.SimplicialThickening
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  {n : ℕ} (R : EnrichedFunctor SSet.{u} D C)

/-- 相対ホーンの各頂点の段は、底の元の単調写像の同じ頂点の値に一致する。 -/
lemma quillenCfInitialHorn_vertex_level
    (τQ : (Λ[n + 2, 0] : SSet.{max u v}) ⟶ QuillenCfCollageInfinity R)
    (β : (Δ[n + 2] : SSet.{max u v}) ⟶ Δ[1])
    (sq : CommSq τQ (Λ[n + 2, 0]).ι
      (quillenCfCollageProjection R) β) (a : Fin (n + 3)) :
    (match (hornObj τQ a).obj with
      | .inl _ => (0 : Fin 2)
      | .inr _ => 1) =
    (β.app (Opposite.op ⦋n + 2⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋n + 2⦌))).down.toOrderHom a := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
    (hornVertex (0) a)) sq.w
  change (quillenCfCollageProjection R).app _
    (τQ.app _ (hornVertex (0) a)) =
      β.app _ (stdSimplex.obj₀Equiv.symm a) at h
  rw [← coherentNerveVertex_object
    (τQ.app _ (hornVertex (0) a)), quillenCfCollageProjection_vertex,
    standardSimplexMap_vertex] at h
  have ho : coherentNerveObject (τQ.app _ (hornVertex (0) a)) =
      hornObj τQ a := rfl
  rw [ho] at h
  cases hz : (hornObj τQ a).obj with
  | inl X =>
    simp only [hz] at h
    exact (stdSimplex.obj₀Equiv.{max u v} (n := 1)).symm.injective h
  | inr Y =>
    simp only [hz] at h
    exact (stdSimplex.obj₀Equiv.{max u v} (n := 1)).symm.injective h

/-- 段が一の対象は上段の cf 対象である。 -/
lemma quillenCfCollage_exists_top_of_level_one (Z : QuillenCfCollage R)
    (h : (match Z.obj with
      | .inl _ => (0 : Fin 2)
      | .inr _ => 1) = 1) :
    ∃ Y : CofibrantFibrantObjects D, Z = (quillenCfCollageTop R).obj Y := by
  rcases Z with ⟨Z, hZ⟩
  rcases Z with X | Y
  · exact (by decide : ¬ (0 : Fin 2) = 1) h |>.elim
  · exact ⟨⟨Y, hZ⟩, rfl⟩

/-- 固定混合初期辺を持つ相対ホーンの全後半頂点は上段にある。 -/
lemma quillenCfInitialHorn_suffix_top
    (τQ : (Λ[n + 2, 0] : SSet.{max u v}) ⟶ QuillenCfCollageInfinity R)
    (β : (Δ[n + 2] : SSet.{max u v}) ⟶ Δ[1])
    (sq : CommSq τQ (Λ[n + 2, 0]).ι (quillenCfCollageProjection R) β)
    (W : CofibrantFibrantObjects C) (Y : CofibrantFibrantObjects D)
    (f : (quillenCfCollageBottom R).obj W ⟶ (quillenCfCollageTop R).obj Y)
    (hedge : τQ.app (Opposite.op ⦋1⦌) (initialHornEdge n) = (coherentNerveEdge f).edge)
    (a : Fin (n + 3)) (ha : 1 ≤ a) :
    ∃ Z : CofibrantFibrantObjects D, hornObj τQ a = (quillenCfCollageTop R).obj Z := by
  have hp := horn_simplex_obj τQ (initialHornEdge n) (1 : Fin 2)
  change (τQ.app (Opposite.op ⦋1⦌) (initialHornEdge n)).obj ⟨ULift.up 1⟩ =
    hornObj τQ 1 at hp
  rw [hedge] at hp
  have hlevel := quillenCfInitialHorn_vertex_level R τQ β sq 1
  rw [← hp] at hlevel
  have hb1 : (β.app (Opposite.op ⦋n + 2⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋n + 2⦌))).down.toOrderHom a = 1 := by
    apply le_antisymm (Fin.le_last _) _
    exact le_trans hlevel.le ((β.app (Opposite.op ⦋n + 2⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋n + 2⦌))).down.toOrderHom.monotone ha)
  apply quillenCfCollage_exists_top_of_level_one R
  rw [quillenCfInitialHorn_vertex_level R τQ β sq a, hb1]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
