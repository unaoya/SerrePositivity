module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismStage
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：prism の一段を貼る際の既存部分の逆像のホーンへの包含。
方針：境界部分では欠ける係数頂点を、前の最大単体では欠ける零時刻の頂点を使う。
規約：切替位置 k のセルで欠ける面は k+1 番目。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） の内側ホーン分解。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：初期部分の最大単体への逆像は k+1 番目のホーンに入る。
方針：境界で欠けた係数頂点の持ち上げか、終端で欠ける零時刻の頂点を選ぶ。
規約：最後の切替位置にも成立し、そこでのホーンは外側になる。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、最初の生成部分の逆像の上界。 -/
lemma relativeJoinPrismInitial_preimage_shuffle_le_horn (m : ℕ) (k : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).preimage
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k)) ≤ horn (m + 1) k.succ := by
  rintro ⟨⟨d⟩⟩ a ha
  apply (mem_horn_iff_notMem_range a k.succ).mpr
  rcases ha with ha | ha
  · obtain ⟨b, hb⟩ := ha
    obtain ⟨v, hv⟩ := (mem_boundary_iff_notMem_range b.2.val).mp b.2.property
    refine ⟨k.succ.succAbove v, Fin.succAbove_ne _ _, ?_⟩
    rintro ⟨i, hi⟩
    apply hv
    refine ⟨i, ?_⟩
    have he := congrArg (fun z : ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋d⦌ ↦ z.2 i) hb
    change b.2.val i = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).2 (a i) at he
    rw [hi] at he
    exact he.trans (congrArg (fun h : ⦋m⦌ ⟶ ⦋m⦌ ↦ h.toOrderHom v)
      (SimplexCategory.δ_comp_σ_succ (i := k)))
  · obtain ⟨b, hb⟩ := ha
    refine ⟨k.castSucc, (by
      intro he
      have hv := congrArg Fin.val he
      change k.val = k.val + 1 at hv
      omega), ?_⟩
    rintro ⟨i, hi⟩
    have he := congrArg (fun z : ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋d⦌ ↦ (z.1 i).val) hb
    change 1 = ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).1 (a i)).val at he
    rw [hi, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_time_zero_iff.{u} m k k.castSucc).mpr le_rfl] at he
    omega

/-- 概要：前の最大単体の像の逆像は k 番目の頂点を欠く面に入る。
方針：切替位置 k の零時刻の係数 k は前の最大単体の零時刻の頂点では表せない。
規約：j の切替位置が k より小さいことを要求する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、前のセルとの交わりの上界。 -/
lemma relativeJoinPrismShuffle_preimage_previous_le_face (m : ℕ) (j k : Fin (m + 1))
    (hjk : j < k) :
    (Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m j)).preimage
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k)) ≤
      stdSimplex.face {k.castSucc}ᶜ := by
  rintro ⟨⟨d⟩⟩ a ha
  obtain ⟨b, hb⟩ := (Subcomplex.mem_ofSimplex_obj_iff _ _).mp ha
  rw [stdSimplex.mem_face_iff]
  intro i
  simp only [Finset.mem_compl, Finset.mem_singleton]
  intro hi
  have he := congrArg (fun z : ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋d⦌ ↦
    (z.1 i, z.2 i)) hb
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m j).1 (b.toOrderHom i),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m j).2 (b.toOrderHom i)) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).1 (a i),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).2 (a i)) at he
  rw [hi] at he
  have ht : ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m j).1 (b.toOrderHom i)).val = 0 := by
    have he' := congrArg (fun p : Fin 2 × Fin (m + 1) ↦ p.1.val) he
    exact he'.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_time_zero_iff.{u} m k k.castSucc).mpr le_rfl)
  have hb' := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_time_zero_iff.{u} m j (b.toOrderHom i)).mp ht
  have hv := congrArg (fun p : Fin 2 × Fin (m + 1) ↦ p.2.val) he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_coefficient_val, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_coefficient_val,
    ite_eq_left hb', ite_eq_left le_rfl] at hv
  have hj : j.val < k.val := hjk
  have hbi : (b.toOrderHom i).val ≤ j.val := hb'
  change (b.toOrderHom i).val = k.val at hv
  omega

/-- 概要：セル k を追加する前の段階の逆像は k+1 番目のホーンに入る。
方針：初期部分の上界と、前のセルの逆像が k 番目の面に入ることを合わせる。
規約：逆像の等式のうち既存部分からホーンへの方向を結論する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、単一ホーンの pushout の逆像の上界。 -/
lemma relativeJoinPrismStage_preimage_shuffle_le_horn (m : ℕ) (k : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m k.val).preimage
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k)) ≤ horn (m + 1) k.succ := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage, Subcomplex.preimage_max, Subcomplex.preimage_iSup]
  apply sup_le (relativeJoinPrismInitial_preimage_shuffle_le_horn m k)
  apply iSup_le
  intro j
  exact (relativeJoinPrismShuffle_preimage_previous_le_face m j.val k j.property).trans
    (face_le_horn _ _ (by
      intro he
      have hv := congrArg Fin.val he
      change k.val = k.val + 1 at hv
      omega))

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
