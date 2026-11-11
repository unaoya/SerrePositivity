module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLabelPathCoordinates

/-!
概要：中間ラベルと最後の零ラベルの二座標には、次数ごとの有限な切断がある。
方針：零ラベルの初期区間と、任意に追加する中間点から native path を作る。
規約：全 K の単射性は主張しない。固定 K 頂点での高次パラメーター回収に使う。
使われ方：実 encoder の単射性を調べるための有限座標の回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 最初の n+1 個を零、次を中間、最後を終点とする三対象ラベル。 -/
def trianglePrismLabel (n : ℕ) : Fin (n + 3) →o Fin 3 where
  toFun i := if i.val ≤ n then 0 else if i.val = n + 1 then 1 else 2
  monotone' := by
    intro i j hij
    dsimp only
    split_ifs <;> omega

lemma trianglePrismLabel_zero (n : ℕ) : trianglePrismLabel n 0 = 0 := by
  simp [trianglePrismLabel]

/-- 区間座標と零側の最大点を指定した、実 native path。 -/
def trianglePrismCoordinatePath (n : ℕ) (b : Fin 2) (k : Fin (n + 1)) :
    Path (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) (ULift.up (Fin.last (n + 2))) where
  I := {i | i.down.val ≤ k.val ∨ i.down.val = n + 2 ∨ (b = 1 ∧ i.down.val = n + 1)}
  left := Or.inl (Nat.zero_le _)
  right := Or.inr (Or.inl rfl)
  left_le := fun i _ => Fin.zero_le i.down
  le_right := fun i _ => Fin.le_last i.down

lemma trianglePrismCoordinatePath_mono (n : ℕ) {b c : Fin 2} {k l : Fin (n + 1)}
    (hb : b ≤ c) (hk : k ≤ l) :
    (trianglePrismCoordinatePath.{u} n b k).I ⊆ (trianglePrismCoordinatePath n c l).I := by
  intro i hi
  change i.down.val ≤ k.val ∨ i.down.val = n + 2 ∨ (b = 1 ∧ i.down.val = n + 1) at hi
  change i.down.val ≤ l.val ∨ i.down.val = n + 2 ∨ (c = 1 ∧ i.down.val = n + 1)
  rcases hi with hi | hi | ⟨hb', hi⟩
  · exact Or.inl (le_trans hi hk)
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr ⟨by omega, hi⟩)

lemma trianglePrismCoordinatePath_middle (n : ℕ) (b : Fin 2) (k : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle (trianglePrismLabel n) (trianglePrismCoordinatePath.{u} n b k) = b := by
  classical
  have h : (∃ i : Fin (n + 3),
      ULift.up i ∈ (trianglePrismCoordinatePath.{u} n b k).I ∧ trianglePrismLabel n i = 1) ↔ b = 1 := by
    constructor
    · rintro ⟨i, hi, ht⟩
      change i.val ≤ k.val ∨ i.val = n + 2 ∨ (b = 1 ∧ i.val = n + 1) at hi
      simp only [trianglePrismLabel, OrderHom.coe_mk] at ht
      split_ifs at ht <;> simp_all <;> omega
    · intro hb
      refine ⟨⟨n + 1, by omega⟩, Or.inr (Or.inr ⟨hb, rfl⟩), ?_⟩
      simp [trianglePrismLabel]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle, h]
  split_ifs <;> omega

lemma trianglePrismCoordinatePath_lastZero (n : ℕ) (b : Fin 2) (k : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel (trianglePrismLabel n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero _ (trianglePrismLabel_zero n))
      (trianglePrismCoordinatePath.{u} n b k) = k.castAdd 2 := by
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel (trianglePrismLabel n)
  let P := trianglePrismCoordinatePath.{u} n b k
  have hzero : t 0 = 0 := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero _ (trianglePrismLabel_zero n)
  have hz (i : Fin (n + 3)) : t i = 0 ↔ i.val ≤ n := by
    dsimp [t, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel, trianglePrismLabel]
    split_ifs <;> simp_all <;> omega
  apply le_antisymm
  · have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero _ (trianglePrismLabel_zero n)) P
    have ht := (hz _).mp hs.1
    have hp := hs.2
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hzero P).val ≤ k.val ∨
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hzero P).val = n + 2 ∨
      (b = 1 ∧ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hzero P).val = n + 1) at hp
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hzero P).val ≤ k.val
    omega
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero
    · exact (hz _).mpr (by simp; omega)
    · exact Or.inl (by simp)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
