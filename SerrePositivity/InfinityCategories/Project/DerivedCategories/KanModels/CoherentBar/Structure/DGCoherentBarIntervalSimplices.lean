module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarIntervalOrders
/-!
概要：元の単体の区間制限と面の二段作用を、同じ bar ラベルの厳密な等号へ送る。
方針：区間順序写像の合成・面との交換を、元の単体的集合の関手性で評価する。
規約：添字・元の単体・全ラベルを保持し、h 圏の同型には弱めない。
使われ方：bar MC の二重和で同じ標的を持つ項を照合する。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {I : SSet.{u}}

lemma dgCoherentBarSimplex_map_comp {n m l : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (β : ⦋l⦌ ⟶ ⦋m⦌) (s : I _⦋n⦌) :
    I.map β.op (I.map α.op s) = I.map (β ≫ α).op s := by
  have h := ConcreteCategory.congr_hom (I.map_comp α.op β.op) s
  simpa only [← op_comp, types_comp_apply] using h.symm

def dgCoherentBarInterval {n : ℕ} (s : I _⦋n⦌) (a l : ℕ) (h : a + l ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I :=
  ⟨l, I.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder n a l h)).op s⟩

lemma dgCoherentBarPrefix_interval {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s k h = dgCoherentBarInterval s 0 k (by omega) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix dgCoherentBarInterval
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder_interval]

lemma dgCoherentBarTail_interval {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s k h = dgCoherentBarInterval s k (n - k) (by omega) := rfl

lemma dgCoherentBarInterval_comp {n : ℕ} (s : I _⦋n⦌) (a l b m : ℕ)
    (h : a + l ≤ n) (h' : b + m ≤ l) :
    dgCoherentBarInterval (dgCoherentBarInterval s a l h).2 b m h' =
      dgCoherentBarInterval s (a + b) m (by omega) := by
  unfold dgCoherentBarInterval
  congr 1
  change I.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder l b m h')).op
    (I.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder n a l h)).op s) = _
  rw [dgCoherentBarSimplex_map_comp]
  have hc : SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder l b m h') ≫
      SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder n a l h) =
      SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder n (a + b) m (by omega)) :=
    SimplexCategory.Hom.ext _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder_comp n a l b m h h')
  rw [hc]

lemma dgCoherentBarInterval_face {n : ℕ} (s : I _⦋n + 1⦌) (a l : ℕ)
    (h : a + l ≤ n) (i : Fin (l + 2)) :
    dgCoherentBarInterval (I.δ (⟨a + i.val, by omega⟩ : Fin (n + 2)) s) a l h =
      (⟨l, I.δ i (dgCoherentBarInterval s a (l + 1) (by omega)).2⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) := by
  unfold dgCoherentBarInterval
  congr 1
  change I.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder n a l h)).op
      (I.map (SimplexCategory.δ (⟨a + i.val, by omega⟩ : Fin (n + 2))).op s) =
    I.map (SimplexCategory.δ i).op
      (I.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder (n + 1) a (l + 1) (by omega))).op s)
  rw [dgCoherentBarSimplex_map_comp, dgCoherentBarSimplex_map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIntervalOrder_face]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
