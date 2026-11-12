module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalChangeBound
public import Mathlib.CategoryTheory.Filtered.Final

/-!
概要：二つの filtered 表示の比較で用いる、可算列による小さい filtered 部分 poset。
方針：出発部分集合と増大列の和集合を取り、列の cofinal 性・小ささを証明する。
規約：二つの表示を結ぶ coherent 列の存在はここでは仮定も結論もしない。
使われ方：P-1 f2、HTT 5.5.4.13 の交互構成の添字側。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {A : Type u} [Preorder A]

/-- 元の出発部分集合を残し、指定列の像を加えた部分 poset。 -/
def sequentialPiece (seed : Set A) (a : ℕ → A) : Set A := seed ∪ Set.range a

omit [Preorder A] in
/-- 出発部分集合の全ての元は、同じ拡大内に残る。 -/
lemma seed_subset_sequentialPiece (seed : Set A) (a : ℕ → A) :
    seed ⊆ sequentialPiece seed a := Set.subset_union_left

/-- 列の最初の項が出発集合を支配すれば、列は拡大の全ての元を支配する。 -/
lemma sequentialPiece_exists_le (seed : Set A) (a : ℕ → A)
    (hseed : ∀ x ∈ seed, x ≤ a 0) (x : sequentialPiece seed a) :
    ∃ n, x.val ≤ a n := by
  rcases x.property with hx | ⟨n, hn⟩
  · exact ⟨0, hseed x.val hx⟩
  · exact ⟨n, hn.ge⟩

/-- 元の列を拡大された部分 poset の中の列として読む。 -/
def sequentialPieceSequence (seed : Set A) (a : ℕ → A) : ℕ → sequentialPiece seed a :=
  fun n ↦ ⟨a n, Or.inr ⟨n, rfl⟩⟩

/-- 元の増大列の単調性は拡大内でも同じ不等式。 -/
lemma sequentialPieceSequence_monotone (seed : Set A) {a : ℕ → A} (ha : Monotone a) :
    Monotone (sequentialPieceSequence seed a) := fun _ _ h ↦ ha h

/-- 増大列が出発集合を支配すれば、和集合は空でない filtered な部分 poset。 -/
lemma sequentialPiece_isFiltered (seed : Set A) {a : ℕ → A} (ha : Monotone a)
    (hseed : ∀ x ∈ seed, x ≤ a 0) : IsFiltered (sequentialPiece seed a) := by
  have : Nonempty (sequentialPiece seed a) := ⟨sequentialPieceSequence seed a 0⟩
  have : IsDirectedOrder (sequentialPiece seed a) := by
    constructor
    intro x y
    obtain ⟨m, hm⟩ := sequentialPiece_exists_le seed a hseed x
    obtain ⟨n, hn⟩ := sequentialPiece_exists_le seed a hseed y
    exact ⟨sequentialPieceSequence seed a (max m n),
      hm.trans (ha (le_max_left _ _)), hn.trans (ha (le_max_right _ _))⟩
  infer_instance

/-- 元の増大列は拡大された部分 poset の中で final な図式となる。 -/
lemma sequentialPieceSequence_final (seed : Set A) {a : ℕ → A} (ha : Monotone a)
    (hseed : ∀ x ∈ seed, x ≤ a 0) :
    (sequentialPieceSequence_monotone seed ha).functor.Final :=
  (Monotone.final_functor_iff (sequentialPieceSequence_monotone seed ha)).mpr
    (sequentialPiece_exists_le seed a hseed)

omit [Preorder A] in
/-- 非可算濃度未満の出発集合に可算列を加えても、同じ濃度未満に留まる。 -/
lemma sequentialPiece_hasCardinalLT {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (seed : Set A) (hseed : HasCardinalLT seed κ)
    (a : ℕ → A) : HasCardinalLT (sequentialPiece seed a) κ := by
  have hNat : HasCardinalLT (ULift.{u} ℕ) κ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] using hκ
  have hrange : HasCardinalLT (Set.range a) κ :=
    hNat.of_surjective (fun n ↦ (⟨a n.down, ⟨n.down, rfl⟩⟩ : Set.range a)) (by
      rintro ⟨x, n, rfl⟩
      exact ⟨ULift.up n, rfl⟩)
  exact hasCardinalLT_union hκ.le hseed hrange

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
