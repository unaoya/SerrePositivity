module
public import SerrePositivity.KST.Fibration.WeakStringTailCanonicalComponents
public import SerrePositivity.KST.Fibration.FinSnocProductIso

/-! # 元の全連続 cofiber を保持する有限 W 列比較の帰納式 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 最後の面射に沿う先行連続辺は、元の長い列の同じ添字の連続辺である。 -/
lemma consecutiveWeakStringEdge_lastFace (n : ℕ) (i : Fin (n + 1)) :
    consecutiveWeakStringEdge (n + 1) i ≫ SimplexCategory.δ (Fin.last (n + 2)) =
      consecutiveWeakStringEdge (n + 2) i.castSucc := by
  ext j
  have hj : j.val < 2 := j.isLt
  change ((Fin.last (n + 2)).succAbove ⟨i.val + j.val, by omega⟩).val = i.val + j.val
  simp

/-- 元の先行列への制限とその有限比較は、同じ初期頂点・全先行 cofiber の射対。 -/
lemma weakStringFiniteComparison_prefix {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    (multiRealizationFunctor r).map
      (weakStringExactMap q (SimplexCategory.δ (Fin.last (n + 2)))) ≫
      weakStringFiniteComparison q (n + 1) r =
        lift ((multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋n + 2⦌ 0))
          (Pi.lift (fun i : Fin (n + 1) => weakStringCofiberMultiMap q
            (consecutiveWeakStringEdge (n + 2) i.castSucc) r)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, weakStringFiniteComparison_reindex_initial, lift_fst]
    rfl
  · apply Pi.hom_ext
    intro i
    rw [Category.assoc, Category.assoc, weakStringFiniteComparison_reindex_cofiber,
      lift_snd, Pi.lift_comp_π, consecutiveWeakStringEdge_lastFace]

/-- 最後の有限積因子を取り出すと、元の全 cofiber の順序を保つ射対になる。 -/
lemma weakStringFiniteComparison_snoc {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    weakStringFiniteComparison q (n + 2) r ≫
      (𝟙 _ ⊗ₘ (finSnocProductIso ((multiRealizationFunctor r).obj
        (closedStableModel (kernelClosedPredicate q))) (n + 1)).hom) =
      lift ((multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋n + 2⦌ 0))
        (lift (Pi.lift (fun i : Fin (n + 1) => weakStringCofiberMultiMap q
          (consecutiveWeakStringEdge (n + 2) i.castSucc) r))
          (weakStringCofiberMultiMap q
            (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1))) r)) := by
  unfold weakStringFiniteComparison weakStringConsecutiveCofibers
  rw [lift_map, Category.comp_id, finSnocProductIso_lift]

/-- 元の有限積比較は、元の先行列と最後の cofiber の比較の帰納合成である。 -/
lemma weakStringFiniteComparison_factor {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    weakStringTailMultiStep q n r ≫ (weakStringFiniteComparison q (n + 1) r ⊗ₘ 𝟙 _) ≫
      (α_ _ _ _).hom = weakStringFiniteComparison q (n + 2) r ≫
        (𝟙 _ ⊗ₘ (finSnocProductIso ((multiRealizationFunctor r).obj
          (closedStableModel (kernelClosedPredicate q))) (n + 1)).hom) := by
  rw [weakStringFiniteComparison_snoc, weakStringTailMultiStep_canonical]
  rw [← Category.assoc, lift_map, Category.comp_id, weakStringFiniteComparison_prefix,
    lift_lift_associator_hom]

end SerrePositivity.KST.Fibration
