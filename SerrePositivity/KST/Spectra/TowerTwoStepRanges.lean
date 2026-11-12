module

public import SerrePositivity.KST.Spectra.TowerMittagLefflerComparison

/-!
概要：二段の像の一致を反復し、合成遷移の像の安定化を導く。
方針：一段下の射影を保つ持ち上げを、さらに下への合成射で送る。
規約：群の可換性は不要。二段の局所的な持ち上げだけを入力にする。
使われ方：Goerss–Jardine VIII §§1–2。fiber 微分の完全性から Mittag–Leffler 条件へ。
-/

@[expose] public section
universe u
open CategoryTheory Opposite

namespace SerrePositivity.KST.Spectra.TowerLimOne

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : ℕ → Type u) [∀ n, Group (G n)] (q : ∀ n, G (n + 1) →* G n)

/-- 隣接する合成遷移は元の遷移。 -/
lemma transitionLE_step (n : ℕ) (a : G (n + 1)) :
    transitionLE G q n (n + 1) (Nat.le_succ n) a = q n a := by
  dsimp only [transitionLE, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.groupTower_step]
  rfl

/-- 次段からの合成遷移の値は、隣接射の後の合成遷移で計算できる。 -/
lemma transitionLE_step_comp (n m : ℕ) (h : n ≤ m) (a : G (m + 1)) :
    transitionLE G q n (m + 1) (h.trans (Nat.le_succ m)) a =
      transitionLE G q n m h (q m a) := by
  have he : (homOfLE (h.trans (Nat.le_succ m))).op =
      (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
  dsimp only [transitionLE]
  rw [he, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition_comp]
  have hs : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q (homOfLE (Nat.le_succ m)).op a = q m a :=
    transitionLE_step G q m a
  rw [hs]

/-- 局所的に一段下の像を保つ持ち上げがあれば、合成射の隣接する像も等しい。 -/
lemma range_step_eq_of_two_step_lifting
    (hlift : ∀ m, ∀ a : G (m + 1), ∃ b : G (m + 2), q m (q (m + 1) b) = q m a)
    (n m : ℕ) (h : n ≤ m) :
    Set.range (transitionLE G q n (m + 1) (h.trans (Nat.le_succ m))) =
      Set.range (transitionLE G q n (m + 2) (by omega)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hlift m a
    refine ⟨b, ?_⟩
    rw [transitionLE_step_comp G q n (m + 1) (by omega),
      transitionLE_step_comp G q n m h, transitionLE_step_comp G q n m h, hb]
  · rintro _ ⟨b, rfl⟩
    exact ⟨q (m + 1) b, (transitionLE_step_comp G q n (m + 1) (by omega) b).symm⟩

/-- 局所的な二段の持ち上げから、一段先以降の全ての像の安定化を得る。 -/
lemma stable_ranges_of_two_step_lifting
    (hlift : ∀ m, ∀ a : G (m + 1), ∃ b : G (m + 2), q m (q (m + 1) b) = q m a)
    (n m : ℕ) (h : n + 1 ≤ m) :
    Set.range (transitionLE G q n (n + 1) (Nat.le_succ n)) =
      Set.range (transitionLE G q n m (by omega)) := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m h ih =>
    apply ih.trans
    cases m with
    | zero => omega
    | succ k => exact range_step_eq_of_two_step_lifting G q hlift n k (by omega)

/-- 二段の持ち上げ条件を持つ群の塔は Mittag–Leffler。 -/
theorem isMittagLeffler_of_two_step_lifting
    (hlift : ∀ m, ∀ a : G (m + 1), ∃ b : G (m + 2), q m (q (m + 1) b) = q m a) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler G q := by
  apply isMittagLeffler_of_stable_ranges
  intro n
  exact ⟨n + 1, Nat.le_succ n, fun k h ↦ stable_ranges_of_two_step_lifting G q hlift n k h⟩

end
end SerrePositivity.KST.Spectra.TowerLimOne
