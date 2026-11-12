module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FlagIso

/-!
概要：旗の頂点集合と単射な頂点写像による解像の像。
方針：旗の最後の集合を台とし、単射な直接像の逆像を取って旗を回収する。
規約：ここでは標準単体間の写像を扱う。一般の単体集合の単射保存は別に示す。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、解像の境界と貼り合わせの準備。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：旗が使う全ての頂点の有限集合。
方針：包含方向に増大する旗の最後の集合を取る。
規約：旗の次数 d に対する最後の段は Fin.last d。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、解像の境界の組み合わせ論的な記述。 -/
def CoherentResolutionFlag.support {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    Finset (Fin (n + 1)) := F.sets (Fin.last d)

/-- 概要：旗の各段は台に含まれる。
方針：最後の段への包含を使う。
規約：零次の段も含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、旗の台を使う像の判定。 -/
lemma CoherentResolutionFlag.sets_subset_support {n d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (k : Fin (d + 1)) : F.sets k ⊆ F.support :=
  F.monotone_sets (Fin.le_last k)

/-- 概要：旗の引き戻しは台を増やさない。
方針：選択した最後の集合は元の台に含まれ、切り詰めは点を除くだけ。
規約：任意の面と退化の引き戻しを含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、真部分集合を台とする旗の部分複体。 -/
lemma CoherentResolutionFlag.support_pullback_subset {n d e : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    (F.pullback α).support ⊆ F.support := by
  intro k hk
  exact F.sets_subset_support _ (Finset.mem_filter.mp hk).1

/-- 概要：旗の直接像の台は元の台の直接像。
方針：最後の集合で直接像の定義を評価する。
規約：頂点写像の単射性は不要。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、台による解像の像の判定。 -/
lemma CoherentResolutionFlag.support_pushforward {n m d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (β : Fin (n + 1) →o Fin (m + 1)) :
    (F.pushforward β).support = F.support.image β := rfl

/-- 概要：単射な頂点写像による旗の直接像は単射。
方針：始点と各段の有限集合を単射な直接像から回収する。
規約：旗の次数 d を固定する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体の面の解像が単射になること。 -/
lemma CoherentResolutionFlag.pushforward_injective {n m d : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Function.Injective (fun F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d ↦ F.pushforward β) := by
  intro F G h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · exact hβ (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.start h)
  · funext k
    exact Finset.image_injective hβ (congrArg (fun H ↦ H.sets k) h)

/-- 概要：単射な頂点写像は旗の解像の間の単射を与える。
方針：各次数で旗の直接像の単射性を適用する。
規約：単体集合の Mono として表す。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の解像の貼り合わせの入力。 -/
lemma coherentResolutionMap_mono {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap.{u} β) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro F G h
  apply ULift.ext
  exact CoherentResolutionFlag.pushforward_injective β hβ (congrArg ULift.down h)

/-- 概要：台が単射な頂点写像の像に入る旗を元の頂点集合へ戻す。
方針：始点の原像を取り、各集合は頂点写像の逆像とする。
規約：単射性により始点の原像は一意で、順序の反映により下界条件を保つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の解像の像の特徴づけ。 -/
noncomputable def CoherentResolutionFlag.preimage {n m d : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag m d)
    (hs : ∀ k ∈ F.support, k ∈ Set.range β) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d := by
  classical
  let s := Classical.choose (hs F.start (F.start_mem (Fin.last d)))
  have hs0 : β s = F.start := Classical.choose_spec (hs F.start (F.start_mem (Fin.last d)))
  refine { start := s, sets := fun k ↦ Finset.univ.filter (fun j ↦ β j ∈ F.sets k)
           monotone_sets := ?_, first := ?_, lower := ?_ }
  · intro k l h j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      F.monotone_sets h (Finset.mem_filter.mp hj).2⟩
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, F.first, Finset.mem_singleton]
    rw [← hs0]
    exact hβ.eq_iff
  · intro k j hj
    have h : β s ≤ β j := hs0.symm ▸ F.lower k (β j) (Finset.mem_filter.mp hj).2
    exact (β.monotone.strictMono_of_injective hβ).le_iff_le.mp h

/-- 概要：像に台を持つ旗を戻して直接像を取ると元の旗を回収する。
方針：台の各点の原像と各段の逆像の所属を比較する。
規約：原像の選択は単射性によって結果に影響しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の解像の像の十分条件。 -/
lemma CoherentResolutionFlag.preimage_pushforward {n m d : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag m d) (hs : ∀ k ∈ F.support, k ∈ Set.range β) :
    (CoherentResolutionFlag.preimage β hβ F hs).pushforward β = F := by
  classical
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · exact Classical.choose_spec (hs F.start (F.start_mem (Fin.last d)))
  · funext k
    apply Finset.ext
    intro l
    change l ∈ (Finset.univ.filter (fun j ↦ β j ∈ F.sets k)).image β ↔ l ∈ F.sets k
    constructor
    · intro hl
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
      exact (Finset.mem_filter.mp hj).2
    · intro hl
      obtain ⟨j, hj⟩ := hs l (F.sets_subset_support k hl)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hj.symm ▸ hl⟩, hj⟩

/-- 概要：単射な頂点写像の直接像に入る旗は、台がその像に含まれる旗に等しい。
方針：必要性は直接像の所属、十分性は構成した原像を使う。
規約：全ての段ではなく最後の段だけで判定できる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界と面の解像の像の具体的な記述。 -/
lemma CoherentResolutionFlag.mem_range_pushforward_iff {n m d : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag m d) :
    F ∈ Set.range (fun G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d ↦ G.pushforward β) ↔
      ∀ k ∈ F.support, k ∈ Set.range β := by
  constructor
  · rintro ⟨G, rfl⟩ k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨j, rfl⟩
  · intro hs
    exact ⟨CoherentResolutionFlag.preimage β hβ F hs,
      CoherentResolutionFlag.preimage_pushforward β hβ F hs⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
