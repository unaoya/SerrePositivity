module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupportPairing

/-!
概要：可算 spine の頂点集合の pairing に、整礎な辞書式順位を与える。
方針：最大・最小番号の差を先に、頂点数を後に比較する。
規約：無限な添字全体で一つの自然数対の順位を使う。
使われ方：spine の inner horn pairing の正則性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：spine の外では挿入点の両側に元の頂点が存在する。
方針：最小頂点と、元の番号差を実現する大きい頂点を選ぶ。
規約：追加する点は元の端点にはならない。
使われ方：pairing の inner 条件と最大番号の保持。 -/
lemma sequentialSpinePivot_interior {S : Finset ℕ} (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S) :
    ∃ a ∈ S, ∃ b ∈ S, a < _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot S ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot S < b := by
  let hs := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineOutside_nonempty hS
  obtain ⟨a, ha, b, hb, hab⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.not_sequentialSpineSupport_iff S).mp hS
  have hmin := Finset.min'_le S a ha
  refine ⟨S.min' hs, Finset.min'_mem S hs, b, hb, ?_, ?_⟩
  all_goals
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot_eq hs]
    omega

/-- 概要：有限頂点集合の pairing を制御する自然数対の順位。
方針：番号の幅と頂点数を並べ、空集合には既定値を置く。
規約：実際の領域外の集合は常に非空。
使われ方：祖先関係の整礎性を自然数の辞書式順序へ移す。 -/
def sequentialSpineSupportRank (S : Finset ℕ) : ℕ × ℕ :=
  if hS : S.Nonempty then (S.max' hS - S.min' hS, S.card) else (0, 0)

/-- 概要：領域外の集合では順位を最大・最小番号と頂点数で計算できる。
方針：非空分岐を展開する。
規約：非空性の証明の選択に依存しない。
使われ方：祖先関係の順位の具体的な比較。 -/
lemma sequentialSpineSupportRank_eq {S : Finset ℕ} (hS : S.Nonempty) :
    sequentialSpineSupportRank S = (S.max' hS - S.min' hS, S.card) := by
  simp only [sequentialSpineSupportRank, dite_eq_left hS]

/-- 概要：別の対の大きい集合の面となる小さい集合では順位が厳密に下がる。
方針：頂点番号の幅は増えず、幅が同じなら最小番号と挿入点が等しいので頂点数が減る。
規約：小さい集合は自分の挿入点を含まない。
使われ方：単体の祖先関係に対する一つの整礎順位。 -/
lemma sequentialSpineSupportRank_lt (S T : Finset ℕ)
    (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S) (hT : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport T)
    (hST : S ⊆ insert (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot T) T)
    (hpS : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot S ∉ S) (hne : S ≠ T) :
    Prod.Lex (· < ·) (· < ·) (sequentialSpineSupportRank S)
      (sequentialSpineSupportRank T) := by
  let hs := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineOutside_nonempty hS
  let ht := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineOutside_nonempty hT
  obtain ⟨a, ha, b, hb, hap, hpb⟩ := sequentialSpinePivot_interior hT
  have hpb' := Finset.le_max' T b hb
  have hpmin := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot_eq ht
  have hbound (v : ℕ) (hv : v ∈ S) : T.min' ht ≤ v ∧ v ≤ T.max' ht := by
    obtain rfl | hv := Finset.mem_insert.mp (hST hv)
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot_eq ht]
      constructor <;> omega
    · exact ⟨Finset.min'_le T v hv, Finset.le_max' T v hv⟩
  have hmin := (hbound _ (Finset.min'_mem S hs)).1
  have hmax := (hbound _ (Finset.max'_mem S hs)).2
  have hsm := Finset.min'_le_max' S hs
  have htm := Finset.min'_le_max' T ht
  rw [sequentialSpineSupportRank_eq hs, sequentialSpineSupportRank_eq ht]
  by_cases hwidth : S.max' hs - S.min' hs < T.max' ht - T.min' ht
  · exact Prod.Lex.left _ _ hwidth
  · have hmineq : S.min' hs = T.min' ht := by omega
    have hweq : S.max' hs - S.min' hs = T.max' ht - T.min' ht := by omega
    have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot S = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot T := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot_eq hs, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot_eq ht, hmineq]
    have hsub : S ⊆ T := by
      intro v hv
      obtain he | ht := Finset.mem_insert.mp (hST hv)
      · exact False.elim (hpS (by rwa [hp, ← he]))
      · exact ht
    have hc : S.card < T.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    simpa only [hweq] using Prod.Lex.right (T.max' ht - T.min' ht) hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
