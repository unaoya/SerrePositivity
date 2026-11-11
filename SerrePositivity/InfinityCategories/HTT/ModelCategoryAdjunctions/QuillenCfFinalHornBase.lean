module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornLastEdge
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageProjection

/-!
# 相対最終ホーンの前半頂点の下段性

概要：実際の固定最終辺と回収射を照合し、元の相対ホーンへ Hom 持ち上げを適用する。
方針：既知面の自然性・通常の射の抽出・区間の単調性を使う。
規約：ambient の全対象に Hom 条件を仮定せず、元の下段始域について証明する。
使われ方：HTT 5.2.4.6 の Cartesian な持ち上げの構成。豊穣単体の復元は別途必要。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  {n : ℕ} (R : EnrichedFunctor SSet.{u} D C)

/-- 標準単体間の写像の頂点作用は、最大単体の像が表す単調写像で計算できる。 -/
lemma standardSimplexMap_vertex {r s : ℕ}
    (β : (Δ[r] : SSet.{u}) ⟶ Δ[s]) (a : Fin (r + 1)) :
    β.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm a) =
      stdSimplex.obj₀Equiv.symm
        ((β.app (Opposite.op ⦋r⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌))).down.toOrderHom a) := by
  have h := NatTrans.naturality_apply β (SimplexCategory.const ⦋0⦌ ⦋r⦌ a).op
    (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌))
  exact h

/-- 相対ホーンの各頂点の段は、底の元の単調写像の同じ頂点の値に一致する。 -/
lemma quillenCfFinalHorn_vertex_level
    (τQ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R)
    (β : (Δ[n + 2] : SSet.{max u v}) ⟶ Δ[1])
    (sq : CommSq τQ (Λ[n + 2, Fin.last (n + 2)]).ι
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) β) (a : Fin (n + 3)) :
    (match (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τQ a).obj with
      | .inl _ => (0 : Fin 2)
      | .inr _ => 1) =
    (β.app (Opposite.op ⦋n + 2⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋n + 2⦌))).down.toOrderHom a := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornVertex (Fin.last (n + 2)) a)) sq.w
  change (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R).app _
    (τQ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornVertex (Fin.last (n + 2)) a)) =
      β.app _ (stdSimplex.obj₀Equiv.symm a) at h
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
    (τQ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornVertex (Fin.last (n + 2)) a)), _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection_vertex,
    standardSimplexMap_vertex] at h
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (τQ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornVertex (Fin.last (n + 2)) a)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τQ a := rfl
  rw [ho] at h
  cases hz : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τQ a).obj with
  | inl X =>
    simp only [hz] at h
    exact (stdSimplex.obj₀Equiv.{max u v} (n := 1)).symm.injective h
  | inr Y =>
    simp only [hz] at h
    exact (stdSimplex.obj₀Equiv.{max u v} (n := 1)).symm.injective h

/-- 段が零の cf 対応圏の対象は、元の下段 cf 対象の像として表せる。 -/
lemma quillenCfCollage_exists_bottom_of_level_zero (Z : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollage R)
    (h : (match Z.obj with
      | .inl _ => (0 : Fin 2)
      | .inr _ => 1) = 0) :
    ∃ X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C, Z = (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X := by
  rcases Z with ⟨Z, hZ⟩
  rcases Z with X | Y
  · exact ⟨⟨X, hZ⟩, rfl⟩
  · exact (by decide : ¬ (1 : Fin 2) = 0) h |>.elim

/-- 固定最終辺が下段から上段への元の混合辺なら、相対ホーンの全前半頂点は下段にある。 -/
lemma quillenCfFinalHorn_prefix_bottom
    (τQ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R)
    (β : (Δ[n + 2] : SSet.{max u v}) ⟶ Δ[1])
    (sq : CommSq τQ (Λ[n + 2, Fin.last (n + 2)]).ι
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) β)
    (W : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D)
    (f : (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj W ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y)
    (hedge : τQ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (a : Fin (n + 3)) (ha : a ≤ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    ∃ X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τQ a = (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X := by
  have hp := congrArg Sigma.fst (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow_data_of_fixedEdge τQ f hedge)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τQ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) = (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj W at hp
  have hlevel := quillenCfFinalHorn_vertex_level R τQ β sq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
  rw [hp] at hlevel
  have hb0 : (β.app (Opposite.op ⦋n + 2⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋n + 2⦌))).down.toOrderHom a = 0 := by
    apply le_antisymm _ (Fin.zero_le _)
    exact le_trans ((β.app (Opposite.op ⦋n + 2⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋n + 2⦌))).down.toOrderHom.monotone ha) hlevel.ge
  apply quillenCfCollage_exists_bottom_of_level_zero R
  rw [quillenCfFinalHorn_vertex_level R τQ β sq a, hb0]

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
