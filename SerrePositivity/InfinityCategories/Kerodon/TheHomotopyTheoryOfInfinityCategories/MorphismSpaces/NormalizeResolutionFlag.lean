module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLowDimension

/-!
# 増大する有限集合族の旗への正規化

概要：最初の集合の最大元以上に切り詰めると、一般の非空な増大集合族を解像の旗にできる。
方針：最初の最大元が全段に属することを使い、最大元と引き戻しの計算を明示する。
規約：集合族の最初の段は一点集合でなくてもよい。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） の解像の相対的な変形の準備。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：非空な増大集合族を最初の最大元で切り詰めて解像の旗にする。
方針：最初の最大元を始点とし、各段で始点以上の元だけを残す。
規約：非空性は最初の段だけに要求する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の頂点を追加する変形の正規化。 -/
def normalizeResolutionFlag {n d : ℕ} (S : Fin (d + 1) → Finset (Fin (n + 1)))
    (hS : Monotone S) (h0 : (S 0).Nonempty) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d where
  start := (S 0).max' h0
  sets t := (S t).filter ((S 0).max' h0 ≤ ·)
  monotone_sets := by
    intro t r h k hk
    exact Finset.mem_filter.mpr ⟨hS h (Finset.mem_filter.mp hk).1,
      (Finset.mem_filter.mp hk).2⟩
  first := by
    apply Finset.ext
    intro k
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hl⟩
      exact le_antisymm (Finset.le_max' _ _ hk) hl
    · intro hk
      subst k
      exact ⟨Finset.max'_mem _ _, le_rfl⟩
  lower _ _ hk := (Finset.mem_filter.mp hk).2

/-- 概要：正規化しても各段の最大元は変わらない。
方針：元の最大元が切断点以上であり、切り詰めた集合にも属することを使う。
規約：後の段の非空性は最初の段からの包含で得る。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の正規化と面の整合。 -/
lemma normalizeResolutionFlag_maxAt {n d : ℕ}
    (S : Fin (d + 1) → Finset (Fin (n + 1))) (hS : Monotone S)
    (h0 : (S 0).Nonempty) (t : Fin (d + 1)) :
    (normalizeResolutionFlag S hS h0).maxAt t =
      (S t).max' (h0.mono (hS (Fin.zero_le t))) := by
  apply le_antisymm
  · exact Finset.le_max' _ _ (Finset.mem_filter.mp
      ((normalizeResolutionFlag S hS h0).maxAt_mem t)).1
  · apply (normalizeResolutionFlag S hS h0).le_maxAt
    exact Finset.mem_filter.mpr ⟨Finset.max'_mem _ _,
      Finset.le_max' _ _ (hS (Fin.zero_le t) (Finset.max'_mem _ _))⟩

/-- 概要：集合族の正規化は全ての添字の引き戻しと可換である。
方針：二回の切断は後に選んだ段の最大元による一回の切断に等しいと示す。
規約：最初の段を変える面と退化も含む。
使われ方：HA 1.3.1.17 の解像上の変形を単体的な射にするための整合。 -/
lemma normalizeResolutionFlag_pullback {n d e : ℕ}
    (S : Fin (d + 1) → Finset (Fin (n + 1))) (hS : Monotone S)
    (h0 : (S 0).Nonempty) (α : Fin (e + 1) →o Fin (d + 1)) :
    (normalizeResolutionFlag S hS h0).pullback α =
      normalizeResolutionFlag (fun t ↦ S (α t)) (hS.comp α.monotone)
        (h0.mono (hS (Fin.zero_le (α 0)))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · exact normalizeResolutionFlag_maxAt S hS h0 (α 0)
  · funext t
    apply Finset.ext
    intro k
    change k ∈ ((S (α t)).filter ((S 0).max' h0 ≤ ·)).filter
      ((normalizeResolutionFlag S hS h0).maxAt (α 0) ≤ ·) ↔ _
    rw [normalizeResolutionFlag_maxAt]
    simp only [normalizeResolutionFlag, Finset.mem_filter]
    have hcut : (S 0).max' h0 ≤ (S (α 0)).max' (h0.mono (hS (Fin.zero_le (α 0)))) :=
      Finset.le_max' _ _ (hS (Fin.zero_le (α 0)) (Finset.max'_mem _ _))
    exact ⟨fun ⟨⟨hk, _⟩, hl⟩ ↦ ⟨hk, hl⟩,
      fun ⟨hk, hl⟩ ↦ ⟨⟨hk, hcut.trans hl⟩, hl⟩⟩

/-- 概要：解像の旗を集合族として正規化しても元の旗に等しい。
方針：最初の最大元は始点であり、全ての集合の元は既に始点以上である。
規約：既存の旗と新しい正規化の規約を等式で合わせる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の変形の恒等端点の計算。 -/
lemma normalizeResolutionFlag_existing {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    normalizeResolutionFlag F.sets F.monotone_sets (F.sets_nonempty 0) = F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · exact F.maxAt_zero
  · funext t
    apply Finset.ext
    intro k
    change k ∈ (F.sets t).filter (F.maxAt 0 ≤ ·) ↔ k ∈ F.sets t
    rw [F.maxAt_zero]
    exact ⟨fun hk ↦ (Finset.mem_filter.mp hk).1,
      fun hk ↦ Finset.mem_filter.mpr ⟨hk, F.lower t k hk⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
