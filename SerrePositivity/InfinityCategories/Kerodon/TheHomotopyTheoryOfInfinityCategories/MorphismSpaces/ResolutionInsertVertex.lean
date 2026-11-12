module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.NormalizeResolutionFlag

/-!
# 選んだ頂点だけを追加する解像の変形

概要：単位区間の指示に従って各集合に一頂点を追加し、最初の最大元で正規化する。
方針：集合族の増大性と正規化の最大元の計算を使う。
規約：区間全体を埋めず、指定された頂点以外を追加しない。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） のホーン上の相対的な変形。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：単位区間の各段が一なら選んだ頂点を追加して旗を正規化する。
方針：零から一への切り替えで集合が増えることを使う。
規約：最初から一の場合は新しい始点で切り詰める。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホーンの欠落頂点だけを追加する変形。 -/
def resolutionInsertVertex {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (i : Fin (n + 1))
    (t : Fin (d + 1) →o Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.normalizeResolutionFlag (fun k ↦ if t k = 0 then F.sets k else insert i (F.sets k)) (by
    intro a b hab k hk
    by_cases ha : t a = 0 <;> by_cases hb : t b = 0
    · simp only [ite_eq_left ha, ite_eq_left hb] at hk ⊢
      exact F.monotone_sets hab hk
    · simp only [ite_eq_left ha, ite_eq_right hb] at hk ⊢
      exact Finset.mem_insert_of_mem (F.monotone_sets hab hk)
    · exact False.elim (ha (le_antisymm (hb ▸ t.monotone hab) (Fin.zero_le _)))
    · simp only [ite_eq_right ha, ite_eq_right hb] at hk ⊢
      exact Finset.insert_subset_insert i (F.monotone_sets hab) hk) (by
    by_cases h : t 0 = 0
    · simpa only [ite_eq_left h] using F.sets_nonempty 0
    · simpa only [ite_eq_right h] using Finset.insert_nonempty i (F.sets 0))

/-- 概要：頂点を追加する変形の各段の最大元を計算する。
方針：正規化が最大元を保つことと insert の最大元の式を使う。
規約：一の段では元の最大元と選んだ頂点の大きい方を取る。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の引き戻しの新しい切断点の計算。 -/
lemma resolutionInsertVertex_maxAt {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (n + 1)) (t : Fin (d + 1) →o Fin 2) (k : Fin (d + 1)) :
    (resolutionInsertVertex F i t).maxAt k =
      if t k = 0 then F.maxAt k else max i (F.maxAt k) := by
  unfold resolutionInsertVertex
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.normalizeResolutionFlag_maxAt]
  by_cases h : t k = 0
  · simp only [ite_eq_left h]
    rfl
  · simp only [ite_eq_right h, Finset.max'_insert i (F.sets k) (F.sets_nonempty k)]
    rfl

/-- 概要：頂点を追加する変形の始点は最初の段の最大元で決まる。
方針：零段の最大元の式を始点の式へ移す。
規約：途中から一になる場合には元の始点を保つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の正規化後の集合の所属の整理。 -/
lemma resolutionInsertVertex_start {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (n + 1)) (t : Fin (d + 1) →o Fin 2) :
    (resolutionInsertVertex F i t).start =
      if t 0 = 0 then F.start else max i F.start := by
  rw [← (resolutionInsertVertex F i t).maxAt_zero, resolutionInsertVertex_maxAt, F.maxAt_zero]

/-- 概要：頂点を追加した旗の集合は追加後の集合の始点以上への制限である。
方針：正規化の集合と始点の定義を評価する。
規約：切断前の集合と切断点を分けて明示する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の引き戻しの所属の比較。 -/
lemma resolutionInsertVertex_sets {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (n + 1)) (t : Fin (d + 1) →o Fin 2) (k : Fin (d + 1)) :
    (resolutionInsertVertex F i t).sets k =
      (if t k = 0 then F.sets k else insert i (F.sets k)).filter
        ((resolutionInsertVertex F i t).start ≤ ·) := rfl

/-- 概要：一頂点の追加と正規化は旗と単位区間の同時の引き戻しと可換である。
方針：新しい切断点が元の二つの切断点以上なので、切り落とした点は戻らないと示す。
規約：先頭の段を変える面も含む全ての単調写像に適用する。
使われ方：HA 1.3.1.17 の相対的な変形を実際の単体的ホモトピーにまとめる。 -/
lemma resolutionInsertVertex_pullback {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (n + 1)) (t : Fin (d + 1) →o Fin 2)
    (α : Fin (e + 1) →o Fin (d + 1)) :
    (resolutionInsertVertex F i t).pullback α =
      resolutionInsertVertex (F.pullback α) i (t.comp α) := by
  let G := resolutionInsertVertex F i t
  let G' := resolutionInsertVertex (F.pullback α) i (t.comp α)
  have hs : G.maxAt (α 0) = G'.start := by
    rw [resolutionInsertVertex_maxAt, resolutionInsertVertex_start]
    rfl
  have hc : F.maxAt (α 0) ≤ G'.start := by
    rw [← hs, resolutionInsertVertex_maxAt]
    split
    · exact le_rfl
    · exact le_max_right _ _
  have hg : G.start ≤ G'.start :=
    hs ▸ G.le_maxAt (α 0) G.start (G.start_mem (α 0))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext hs
  funext r
  apply Finset.ext
  intro k
  change k ∈ (G.sets (α r)).filter (G.maxAt (α 0) ≤ ·) ↔ k ∈ G'.sets r
  rw [hs, resolutionInsertVertex_sets, resolutionInsertVertex_sets]
  change k ∈ ((if t (α r) = 0 then F.sets (α r) else insert i (F.sets (α r))).filter
    (G.start ≤ ·)).filter (G'.start ≤ ·) ↔
      k ∈ (if t (α r) = 0 then (F.sets (α r)).filter (F.maxAt (α 0) ≤ ·)
        else insert i ((F.sets (α r)).filter (F.maxAt (α 0) ≤ ·))).filter (G'.start ≤ ·)
  by_cases h : t (α r) = 0
  · simp only [ite_eq_left h, Finset.mem_filter]
    exact ⟨fun ⟨⟨hk, _⟩, hl⟩ ↦ ⟨⟨hk, hc.trans hl⟩, hl⟩,
      fun ⟨⟨hk, _⟩, hl⟩ ↦ ⟨⟨hk, hg.trans hl⟩, hl⟩⟩
  · simp only [ite_eq_right h, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hk, _⟩, hl⟩
      exact ⟨hk.elim Or.inl (fun hk ↦ Or.inr ⟨hk, hc.trans hl⟩), hl⟩
    · rintro ⟨hk, hl⟩
      exact ⟨⟨hk.elim Or.inl (fun hk ↦ Or.inr hk.1), hg.trans hl⟩, hl⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
