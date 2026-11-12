module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveListCutHEq
/-!
概要：単射な単調写像は実切断添字の両端・列の順序・内部点条件を保つ。
方針：有限集合と列の像の所属を戻し、元の狭義順序を写す。
規約：指定された元の添字を写す。使われ方：全次元の切断合成の単射に沿う自然性。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 有限集合の指定最小点は単調な像の最小点に写る。 -/
lemma dgNerveCutImageLeast {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a : Fin (m + 1)) (ha : IsLeast (I : Set (Fin (m + 1))) a) :
    IsLeast ((I.image α) : Set (Fin (n + 1))) (α a) := by
  refine ⟨Finset.mem_image.mpr ⟨a, ha.1, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact α.monotone (ha.2 hx)
/-- 有限集合の指定最大点は単調な像の最大点に写る。 -/
lemma dgNerveCutImageGreatest {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (b : Fin (m + 1)) (hb : IsGreatest (I : Set (Fin (m + 1))) b) :
    IsGreatest ((I.image α) : Set (Fin (n + 1))) (α b) := by
  refine ⟨Finset.mem_image.mpr ⟨b, hb.1, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact α.monotone (hb.2 hx)
/-- 昇順の切断列は単射な単調写像で昇順のまま写る。 -/
lemma dgNerveCutImagePairwise {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (hα : Function.Injective α) (L : List (Fin (m + 1))) (ho : L.Pairwise (· < ·)) :
    (L.map α).Pairwise (· < ·) := by
  apply List.pairwise_map.mpr
  exact ho.imp (fun h => (α.monotone.strictMono_of_injective hα) h)
/-- 切断列の全内部点は、像でも同じ内部点条件を満たす。 -/
lemma dgNerveCutImageInterior {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (hα : Function.Injective α) (I : Finset (Fin (m + 1))) (a b : Fin (m + 1))
    (L : List (Fin (m + 1))) (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) :
    ∀ y ∈ L.map α, y ∈ I.image α ∧ α a < y ∧ y < α b := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have h := hc x hx
  have hs := α.monotone.strictMono_of_injective hα
  exact ⟨Finset.mem_image.mpr ⟨x, h.1, rfl⟩, hs h.2.1, hs h.2.2⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
