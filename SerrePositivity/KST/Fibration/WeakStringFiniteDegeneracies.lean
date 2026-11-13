module
public import SerrePositivity.KST.Fibration.WeakStringFaceEdges
public import SerrePositivity.KST.Fibration.WeakStringCofiberDegeneracy

/-! # 元の有限比較の退化作用と挿入した共通 cofiber 関手の零性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 全退化は、有限比較の元の初期頂点を厳密に保つ。 -/
lemma weakStringFiniteComparison_degeneracy_initial {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin (n + 1)) :
    (multiRealizationFunctor r).map (weakStringExactMap q (SimplexCategory.σ i)) ≫
      weakStringFiniteComparison q (n + 1) r ≫ fst _ _ =
        (multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋n⦌ 0) := by
  rw [weakStringFiniteComparison_reindex_initial]
  congr 2

/-- 繰り返し頂点より前の元の cofiber 成分は、全反復でそのまま保存される。 -/
lemma weakStringFiniteComparison_degeneracy_cofiber_before {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin (n + 1)) (j : Fin n) (h : j.val < i.val) :
    (multiRealizationFunctor r).map (weakStringExactMap q (SimplexCategory.σ i)) ≫
      weakStringFiniteComparison q (n + 1) r ≫ snd _ _ ≫ Pi.π _ j.castSucc =
        weakStringCofiberMultiMap q (consecutiveWeakStringEdge n j) r := by
  rw [weakStringFiniteComparison_reindex_cofiber,
    consecutiveWeakStringEdge_degeneracy_before n i j h]

/-- 繰り返し頂点より後の元の cofiber 成分も、全反復でそのまま保存される。 -/
lemma weakStringFiniteComparison_degeneracy_cofiber_after {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin (n + 1)) (j : Fin n) (h : i.val ≤ j.val) :
    (multiRealizationFunctor r).map (weakStringExactMap q (SimplexCategory.σ i)) ≫
      weakStringFiniteComparison q (n + 1) r ≫ snd _ _ ≫ Pi.π _ j.succ =
        weakStringCofiberMultiMap q (consecutiveWeakStringEdge n j) r := by
  rw [weakStringFiniteComparison_reindex_cofiber,
    consecutiveWeakStringEdge_degeneracy_after n i j h]

/-- 挿入された一成分は、元の繰り返し頂点の恒等辺の共通 cofiber 射である。 -/
lemma weakStringFiniteComparison_degeneracy_inserted {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin (n + 1)) :
    (multiRealizationFunctor r).map (weakStringExactMap q (SimplexCategory.σ i)) ≫
      weakStringFiniteComparison q (n + 1) r ≫ snd _ _ ≫ Pi.π _ i =
        weakStringCofiberMultiMap q
          (SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ i) r := by
  rw [weakStringFiniteComparison_reindex_cofiber, consecutiveWeakStringEdge_degeneracy]

/-- 元の退化が挿入する共通核値 cofiber は、全関手圏の実際の零対象である。 -/
theorem weakStringKernelCofiber_degeneracy_inserted_zero {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((weakStringExactMap q (SimplexCategory.σ i) ≫
      weakStringKernelCofiber q (consecutiveWeakStringEdge (n + 1) i)).val)) := by
  rw [weakStringKernelCofiber_reindex, consecutiveWeakStringEdge_degeneracy]
  exact weakStringKernelCofiber_degenerate_isZeroVertex q _

end SerrePositivity.KST.Fibration
