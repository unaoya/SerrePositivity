module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan

/-!
概要：coherent Hom の相対比較に用いる有限部分集合の旗。
方針：最初の集合が一点で、その点が各集合の最小元である増大列を取る。
規約：Mathlib の包含順序に合わせ、Kerodon の旗の順序を反転した右模型を使う。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、Proposition 4.6.7.23（Tag 01LW）、補助構成 Φ の標準単体上の模型。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：最初の集合が最小元一点からなる有限部分集合の増大する旗。
方針：始点、各集合、包含の単調性、始点と下界の条件をまとめる。
規約：n は値域の標準単体の次数、d は旗の単体の次数。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、Mathlib の包含規約での Φ(Δ[n]) の座標。 -/
structure CoherentResolutionFlag (n d : ℕ) where
  /-- 旗の最初の一点。 -/
  start : Fin (n + 1)
  /-- 旗の各段の部分集合。 -/
  sets : Fin (d + 1) → Finset (Fin (n + 1))
  /-- 部分集合は包含方向に増大する。 -/
  monotone_sets : Monotone sets
  /-- 最初の集合は始点のみを含む。 -/
  first : sets 0 = {start}
  /-- 始点は全ての集合の下界。 -/
  lower : ∀ i k, k ∈ sets i → start ≤ k

/-- 概要：旗は始点と各段の集合によって一意に決まる。
方針：二つのデータを置換し、条件の証明の一意性を使う。
規約：次数は両側で共通。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、旗の単体的恒等則と合成則。 -/
@[ext]
lemma CoherentResolutionFlag.ext {n d : ℕ} {F G : CoherentResolutionFlag n d}
    (hstart : F.start = G.start) (hsets : F.sets = G.sets) : F = G := by
  cases F
  cases G
  cases hstart
  cases hsets
  rfl

/-- 概要：始点は旗の全ての集合に属する。
方針：最初の集合の所属を単調性で各段へ写す。
規約：零次の段も含む。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、各段の最大元の存在。 -/
lemma CoherentResolutionFlag.start_mem {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : F.start ∈ F.sets i := by
  apply F.monotone_sets (Fin.zero_le i)
  rw [F.first]
  exact Finset.mem_singleton_self _

/-- 概要：旗の各段の集合は空でない。
方針：始点の所属を使う。
規約：旗の全次数で成立する。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、最大元による射影と引き戻し。 -/
lemma CoherentResolutionFlag.sets_nonempty {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : (F.sets i).Nonempty := ⟨F.start, F.start_mem i⟩

/-- 概要：旗の各段の最大元。
方針：始点を含む有限集合の最大元を取る。
規約：値は Fin(n+1) の元。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、Φ の標準単体への射影。 -/
def CoherentResolutionFlag.maxAt {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : Fin (n + 1) := (F.sets i).max' (F.sets_nonempty i)

/-- 概要：各段の最大元はその段に属する。
方針：有限集合の最大元の所属を使う。
規約：空でないことの証明の選択には依存しない。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、引き戻しの始点の定義。 -/
lemma CoherentResolutionFlag.maxAt_mem {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : F.maxAt i ∈ F.sets i := Finset.max'_mem _ _

/-- 概要：集合の各元はその段の最大元以下。
方針：有限集合の最大元の上界性を使う。
規約：段 i は任意。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、最初の段を切り詰める計算。 -/
lemma CoherentResolutionFlag.le_maxAt {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) (k : Fin (n + 1)) (hk : k ∈ F.sets i) : k ≤ F.maxAt i :=
  Finset.le_max' _ _ hk

/-- 概要：各段の最大元は単調に増加する。
方針：小さい段の最大元を大きい段へ含め、その上界性を使う。
規約：包含順序の旗を使う。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、標準単体への射影の単調性。 -/
lemma CoherentResolutionFlag.maxAt_monotone {n d : ℕ} (F : CoherentResolutionFlag n d) :
    Monotone F.maxAt := by
  intro i j hij
  exact F.le_maxAt j _ (F.monotone_sets hij (F.maxAt_mem i))

/-- 概要：旗の最初の段の最大元は始点。
方針：最初の段が一点集合であることを使う。
規約：旗の引き戻しの恒等則で用いる。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、最初の段の正規化。 -/
lemma CoherentResolutionFlag.maxAt_zero {n d : ℕ} (F : CoherentResolutionFlag n d) :
    F.maxAt 0 = F.start := by
  exact Finset.mem_singleton.mp (F.first ▸ F.maxAt_mem 0)

/-- 概要：単調写像で旗を引き戻し、新しい最初の段の最大元で切り詰める。
方針：選んだ各段を新しい始点以上に制限する。
規約：単純な部分列ではなく、最初の集合が一点になる正規化を含む。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、Φ(Δ[n]) の面と退化の一括定義。 -/
def CoherentResolutionFlag.pullback {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) : CoherentResolutionFlag n e where
  start := F.maxAt (α 0)
  sets i := (F.sets (α i)).filter (fun k ↦ F.maxAt (α 0) ≤ k)
  monotone_sets := by
    intro i j hij k hk
    obtain ⟨hk, hl⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨F.monotone_sets (α.monotone hij) hk, hl⟩
  first := by
    ext k
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hl⟩
      exact le_antisymm (F.le_maxAt _ _ hk) hl
    · rintro rfl
      exact ⟨F.maxAt_mem _, le_rfl⟩
  lower i k hk := (Finset.mem_filter.mp hk).2

/-- 概要：旗の引き戻しの最大元は選んだ元の段の最大元。
方針：切り詰めは最大元を残し、元の最大元を超える点は作らない。
規約：退化によって段が重複しても成立する。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、射影の単体的な自然性。 -/
lemma CoherentResolutionFlag.maxAt_pullback {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (i : Fin (e + 1)) :
    (F.pullback α).maxAt i = F.maxAt (α i) := by
  apply le_antisymm
  · apply F.le_maxAt
    exact (Finset.mem_filter.mp ((F.pullback α).maxAt_mem i)).1
  · apply (F.pullback α).le_maxAt
    apply Finset.mem_filter.mpr
    exact ⟨F.maxAt_mem _, F.maxAt_monotone (α.monotone (Fin.zero_le i))⟩

/-- 概要：恒等写像による旗の引き戻しは元の旗。
方針：最初の最大元は始点であり、始点での切り詰めは集合を変えない。
規約：始点と各段の集合を比較する。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、旗の単体集合の恒等則。 -/
lemma CoherentResolutionFlag.pullback_id {n d : ℕ} (F : CoherentResolutionFlag n d) :
    F.pullback (OrderHom.id (α := Fin (d + 1))) = F := by
  apply CoherentResolutionFlag.ext
  · change F.maxAt 0 = F.start
    exact F.maxAt_zero
  · funext i
    apply Finset.ext
    intro k
    change k ∈ (F.sets i).filter (fun l ↦ F.maxAt 0 ≤ l) ↔ k ∈ F.sets i
    rw [Finset.mem_filter, F.maxAt_zero]
    exact ⟨And.left, fun hk ↦ ⟨hk, F.lower i k hk⟩⟩

/-- 概要：旗の引き戻しは単調写像の合成に反変に整合する。
方針：二段目の切断点は一段目以上なので二重の切り詰めを一度にまとめる。
規約：任意の単調写像に対して成立する。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、旗の単体集合の合成則。 -/
lemma CoherentResolutionFlag.pullback_comp {n d e f : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (β : Fin (f + 1) →o Fin (e + 1)) :
    (F.pullback α).pullback β = F.pullback (α.comp β) := by
  apply CoherentResolutionFlag.ext
  · change (F.pullback α).maxAt (β 0) = F.maxAt (α (β 0))
    exact F.maxAt_pullback α (β 0)
  · funext i
    apply Finset.ext
    intro k
    change k ∈ ((F.sets (α (β i))).filter (fun l ↦ F.maxAt (α 0) ≤ l)).filter
      (fun l ↦ (F.pullback α).maxAt (β 0) ≤ l) ↔
        k ∈ (F.sets (α (β i))).filter (fun l ↦ F.maxAt (α (β 0)) ≤ l)
    rw [F.maxAt_pullback]
    simp only [Finset.mem_filter]
    have hab := F.maxAt_monotone (α.monotone (Fin.zero_le (β 0)))
    exact ⟨fun ⟨⟨hk, _⟩, hb⟩ ↦ ⟨hk, hb⟩,
      fun ⟨hk, hb⟩ ↦ ⟨⟨hk, hab.trans hb⟩, hb⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
