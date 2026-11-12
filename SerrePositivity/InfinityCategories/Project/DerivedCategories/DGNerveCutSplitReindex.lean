module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutSplit
/-!
概要：選択点を含む切断集合と左右の切断集合の対を比較する。
方針：同じ有限集合の左右分割と和集合を実同値として有限和を移す。
規約：元の実切断集合と cochain を使う。使われ方：全次元 tensor 候補の HA の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped BigOperators
/-- 同じ実切断の符号と有限和の添字の比較。 -/
abbrev DGNerveSelectedCutSubsets {α : Type u} [LinearOrder α] (T : Finset α) (j : α) :=
  {S : Finset α // S ⊆ T ∧ j ∈ S}
/-- 同じ実切断の符号と有限和の添字の比較。 -/
abbrev DGNerveSideCutSubsets {α : Type u} [LinearOrder α] (T : Finset α) (p : α → Prop)
    [DecidablePred p] := {S : Finset α // S ⊆ T.filter p}
/-- 同じ実切断の符号と有限和の添字の比較。 -/
def dgNerveCutSplitEquiv {α : Type u} [LinearOrder α] (T : Finset α) (j : α)
    (hj : j ∈ T) :
    DGNerveSelectedCutSubsets T j ≃
      DGNerveSideCutSubsets T (· < j) × DGNerveSideCutSubsets T (j < ·) where
  toFun S := (⟨S.val.filter (· < j), by
      intro x hx
      exact Finset.mem_filter.mpr ⟨S.property.1 (Finset.mem_filter.mp hx).1,
        (Finset.mem_filter.mp hx).2⟩⟩,
    ⟨S.val.filter (j < ·), by
      intro x hx
      exact Finset.mem_filter.mpr ⟨S.property.1 (Finset.mem_filter.mp hx).1,
        (Finset.mem_filter.mp hx).2⟩⟩)
  invFun P := ⟨insert j (P.1.val ∪ P.2.val), by
    refine ⟨Finset.insert_subset hj ?_, Finset.mem_insert_self _ _⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp (P.1.property hx)).1
    · exact (Finset.mem_filter.mp (P.2.property hx)).1⟩
  left_inv S := by
    apply Subtype.ext
    change insert j (S.val.filter (· < j) ∪ S.val.filter (j < ·)) = S.val
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨hx, _⟩ | ⟨hx, _⟩)
      · exact S.property.2
      · exact hx
      · exact hx
    · intro hx
      rcases lt_trichotomy x j with h | h | h
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨hx, h⟩)
  right_inv P := by
    apply Prod.ext <;> apply Subtype.ext
    · change (insert j (P.1.val ∪ P.2.val)).filter (· < j) = P.1.val
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨rfl | hx | hx, hxj⟩
        · exact False.elim (lt_irrefl _ hxj)
        · exact hx
        · exact False.elim (lt_asymm hxj (Finset.mem_filter.mp (P.2.property hx)).2)
      · intro hx
        exact ⟨Or.inr (Or.inl hx), (Finset.mem_filter.mp (P.1.property hx)).2⟩
    · change (insert j (P.1.val ∪ P.2.val)).filter (j < ·) = P.2.val
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨rfl | hx | hx, hjx⟩
        · exact False.elim (lt_irrefl _ hjx)
        · exact False.elim (lt_asymm (Finset.mem_filter.mp (P.1.property hx)).2 hjx)
        · exact hx
      · intro hx
        exact ⟨Or.inr (Or.inr hx), (Finset.mem_filter.mp (P.2.property hx)).2⟩
/-- 同じ実切断の符号と有限和の添字の比較。 -/
lemma dgNerveCutSplit_sum {α : Type u} [Fintype α] [LinearOrder α]
    (T : Finset α) (j : α) (hj : j ∈ T) {M : Type v} [AddCommMonoid M]
    (F : DGNerveSideCutSubsets T (· < j) → DGNerveSideCutSubsets T (j < ·) → M) :
    (∑ S : DGNerveSelectedCutSubsets T j,
      F ((dgNerveCutSplitEquiv T j hj) S).1 ((dgNerveCutSplitEquiv T j hj) S).2) =
      ∑ L, ∑ R, F L R := by
  calc
    _ = ∑ P : DGNerveSideCutSubsets T (· < j) × DGNerveSideCutSubsets T (j < ·),
        F P.1 P.2 := Equiv.sum_comp (dgNerveCutSplitEquiv T j hj) (fun P => F P.1 P.2)
    _ = _ := Fintype.sum_prod_type (fun P => F P.1 P.2)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
