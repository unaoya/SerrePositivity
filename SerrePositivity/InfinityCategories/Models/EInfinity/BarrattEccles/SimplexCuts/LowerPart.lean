module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Expanded
public import Mathlib.Data.Finset.Max

/-!
模型。文献の定義との比較は後で
# 最後の垂直辺より前の有限部分

Berger–Fresse §2.2.6–7 の切断の再帰に使う有限集合の制限。
M14 L09a の有限組合せ C01。最大元を除いた部分を Fin へ圧縮して数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 初期区間を元の有限順序へ戻す埋め込み。 -/
def lowerEmbedding {N : ℕ} (a : Fin N) : Fin a.val ↪ Fin N where
  toFun i := ⟨i.val, lt_trans i.isLt a.isLt⟩
  inj' i j h := by
    apply Fin.ext
    exact congrArg (fun z : Fin N => z.val) h

/-- 有限集合のaより前の部分を、Fin a.valへ詰める。 -/
def lowerPart {N : ℕ} (s : Finset (Fin N)) (a : Fin N) : Finset (Fin a.val) :=
  Finset.univ.filter (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerEmbedding a i ∈ s)

@[simp] lemma mem_lowerPart {N : ℕ} (s : Finset (Fin N)) (a : Fin N) (i : Fin a.val) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s a ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerEmbedding a i ∈ s := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart, Finset.mem_filter, Finset.mem_univ, true_and]

lemma lowerPart_compl {N : ℕ} (s : Finset (Fin N)) (a : Fin N) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart sᶜ a = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s a)ᶜ := by
  ext i
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.mem_lowerPart, Finset.mem_compl]

/-- 最大元の前の部分は、元の集合から一つだけ小さい（L09a C01）。 -/
lemma card_lowerPart_of_max {N : ℕ} (s : Finset (Fin N)) (a : Fin N)
    (ha : a ∈ s) (hm : ∀ i ∈ s, i ≤ a) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s a).card + 1 = s.card := by
  have hcard : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s a).card = (s.erase a).card := by
    apply Finset.card_bij (fun i _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerEmbedding a i)
    · intro i hi
      refine Finset.mem_erase.mpr ⟨?_, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.mem_lowerPart s a i).mp hi⟩
      intro h
      have he := congrArg Fin.val h
      change i.val = a.val at he
      exact (ne_of_lt i.isLt) he
    · intro i _ j _ hij
      exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerEmbedding a).injective hij
    · intro j hj
      have hjm := (Finset.mem_erase.mp hj).2
      have hja : j < a := lt_of_le_of_ne (hm j hjm) (Finset.mem_erase.mp hj).1
      let i : Fin a.val := ⟨j.val, hja⟩
      have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerEmbedding a i = j := Fin.ext rfl
      exact ⟨i, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.mem_lowerPart s a i).mpr (he ▸ hjm), he⟩
  rw [hcard, Finset.card_erase_of_mem ha]
  have hp := Finset.card_pos.mpr ⟨a, ha⟩
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
