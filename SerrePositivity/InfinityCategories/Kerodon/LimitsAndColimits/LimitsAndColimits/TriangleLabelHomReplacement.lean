module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLongHomReplacement

/-!
概要：任意の次数で、零対象から終対象への全 Hom だけを置き換える。
方針：単調な三対象ラベルで変更箇所を判定し、変更される合成則だけを検査する。
規約：次数を二に固定しない。同じラベルが何度現れてもよい。
使われ方：全パラメーターの制御二胞体を、元の二短辺を持つ基準二胞体から構成する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (t : (SimplicialNerve C) _⦋n⦌) (l : Fin (n + 1) →o Fin 3)
  (g : ∀ (i j : Fin (n + 1)), l i = 0 → l j = 2 →
    (nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶
      SimplicialCategory.sHom (t.obj ⟨ULift.up i⟩) (t.obj ⟨ULift.up j⟩)))

/-- 零・終対象間の Hom だけを変更した全次数の Hom データ。 -/
def triangleLabelReplacedHom (i j : Fin (n + 1)) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶
      SimplicialCategory.sHom (t.obj ⟨ULift.up i⟩) (t.obj ⟨ULift.up j⟩) :=
  if hi : l i = 0 then if hj : l j = 2 then g i j hi hj else t.map _ _ else t.map _ _

/-- 変更対象でない Hom は元の作用に一致する。 -/
lemma triangleLabelReplacedHom_proper (i j : Fin (n + 1)) (h : l i ≠ 0 ∨ l j ≠ 2) :
    triangleLabelReplacedHom t l g i j = t.map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  rcases h with h | h
  · simp only [triangleLabelReplacedHom, dite_eq_right h]
  · by_cases hi : l i = 0
    · simp only [triangleLabelReplacedHom, dite_eq_left hi, dite_eq_right h]
    · simp only [triangleLabelReplacedHom, dite_eq_right hi]

/-- 変更対象では指定した同じ Hom の作用を回収する。 -/
lemma triangleLabelReplacedHom_full (i j : Fin (n + 1)) (hi : l i = 0) (hj : l j = 2) :
    triangleLabelReplacedHom t l g i j = g i j hi hj := by
  simp only [triangleLabelReplacedHom, dite_eq_left hi, dite_eq_left hj]

/-- 変更される合成則を検査すれば、同じ対象と他の全 Hom を持つ豊穣関手を得る。 -/
def triangleLabelReplaceLongHoms
    (hg : ∀ (i j k : Fin (n + 1)), i ≤ j → j ≤ k → (hi : l i = 0) → (hk : l k = 2) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up i) (ULift.up j) (ULift.up k) ≫ g i k hi hk =
        (triangleLabelReplacedHom t l g i j ⊗ₘ triangleLabelReplacedHom t l g j k) ≫
          eComp SSet (t.obj ⟨ULift.up i⟩) (t.obj ⟨ULift.up j⟩) (t.obj ⟨ULift.up k⟩)) :
    (SimplicialNerve C) _⦋n⦌ where
  obj := t.obj
  map i j := triangleLabelReplacedHom t l g i.as.down j.as.down
  map_id := by
    rintro ⟨⟨i⟩⟩
    rw [triangleLabelReplacedHom_proper t l g i i (by omega)]
    exact t.map_id _
  map_comp := by
    rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
    by_cases hij : i ≤ j
    swap
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathProduct_empty_hom_ext (ULift.up i) (ULift.up j) (ULift.up k)
        (Or.inl hij) _ _
    by_cases hjk : j ≤ k
    swap
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathProduct_empty_hom_ext (ULift.up i) (ULift.up j) (ULift.up k)
        (Or.inr hjk) _ _
    have h₁ := l.monotone hij
    have h₂ := l.monotone hjk
    by_cases h : l i ≠ 0 ∨ l k ≠ 2
    · rw [triangleLabelReplacedHom_proper t l g i k h,
        triangleLabelReplacedHom_proper t l g i j (by omega),
        triangleLabelReplacedHom_proper t l g j k (by omega)]
      exact t.map_comp _ _ _
    · have hi : l i = 0 := by tauto
      have hk : l k = 2 := by tauto
      rw [triangleLabelReplacedHom_full t l g i k hi hk]
      exact hg i j k hij hjk hi hk

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
