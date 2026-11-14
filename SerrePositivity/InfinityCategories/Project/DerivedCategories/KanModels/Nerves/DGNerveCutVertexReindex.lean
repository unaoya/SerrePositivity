module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutInsertionReindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutSplitReindex
/-!
概要：削除・挿入の全添字を同じ頂点ごとの有限和へ組み替える。
方針：同じ集合・点・cochain を保つ実添字比較を使う。
規約：元の全次数で同定する。使われ方：全次元 HA の右辺の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped BigOperators
/-- 元の全添字と同じ実境界成分の比較。 -/
def dgNerveCutDeletionVertexEquiv {α : Type u} [LinearOrder α] (T : Finset α) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutDeletionIndex T ≃ Σ j : T, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveSelectedCutSubsets T j.val where
  toFun p := ⟨⟨p.val.2, p.property.1 p.property.2⟩, ⟨p.val.1, p.property⟩⟩
  invFun p := ⟨(p.2.val, p.1.val), p.2.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl
/-- 元の全添字と同じ実境界成分の比較。 -/
def dgNerveCutInsertionVertexEquiv {α : Type u} [DecidableEq α] (T : Finset α) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex T ≃ Σ j : T, {S : Finset α // S ⊆ T.erase j.val} where
  toFun p := ⟨⟨p.val.2, p.property.2.1⟩, ⟨p.val.1, fun x hx =>
    Finset.mem_erase.mpr ⟨fun he => p.property.2.2 (by simpa only [he] using hx),
      p.property.1 hx⟩⟩⟩
  invFun p := ⟨(p.2.val, p.1.val),
    (fun _ hx => (Finset.mem_erase.mp (p.2.property hx)).2),
    p.1.property, fun hx => (Finset.mem_erase.mp (p.2.property hx)).1 rfl⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl
/-- 元の全添字と同じ実境界成分の比較。 -/
lemma dgNerveCutDeletionVertex_sum {α : Type u} [Fintype α] [LinearOrder α]
    (T : Finset α) {M : Type v} [AddCommMonoid M] (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutDeletionIndex T → M) :
    (∑ p, f p) = ∑ j : T, ∑ S : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveSelectedCutSubsets T j.val,
      f ((dgNerveCutDeletionVertexEquiv T).symm ⟨j, S⟩) := by
  simpa only [Fintype.sum_sigma] using
    (Equiv.sum_comp (dgNerveCutDeletionVertexEquiv T).symm f).symm
/-- 元の全添字と同じ実境界成分の比較。 -/
lemma dgNerveCutInsertionVertex_sum {α : Type u} [Fintype α] [DecidableEq α]
    (T : Finset α) {M : Type v} [AddCommMonoid M] (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex T → M) :
    (∑ p, f p) = ∑ j : T, ∑ S : {S : Finset α // S ⊆ T.erase j.val},
      f ((dgNerveCutInsertionVertexEquiv T).symm ⟨j, S⟩) := by
  simpa only [Fintype.sum_sigma] using
    (Equiv.sum_comp (dgNerveCutInsertionVertexEquiv T).symm f).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
