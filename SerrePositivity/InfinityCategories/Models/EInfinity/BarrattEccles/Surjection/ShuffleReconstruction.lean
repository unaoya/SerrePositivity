module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ShufflePathUniqueness
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RecoveredPartitionExistence

/-!
模型。文献の定義との比較は後で
# 実際の shuffle 成功項の元データの一意な逆構成

概要：Berger–Fresse §1.5.8–9 の正の内側 arity の逆構成で、元の経路と Schedule まで戻す。
方針：復元両語・分割・両成功を TableCompositionData にまとめ、出力による経路と行長の一意性を使う。
規約：元の成功二表や分割・経路一致は入力に追加しない。
使われ方：TR の一般の部分合成保存で全成功項の全単射を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：同じ元の置換列・挿入位置・合成出力を持つ入力データは等しい（BF §1.5.9）。
方針：両語と分割の一意性で入力を揃え、元の成功 Schedule の一意性を適用する。
規約：TableCompositionData 自身の正の内側語長条件だけを使う。
使われ方：全成功 shuffle 項の逆構成を一意な元の二表と分割へ戻す。 -/
lemma eq_of_same_output {m n d e : ℕ} (c c' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (ho : c.outer = c'.outer) (hi : c.inner = c'.inner) (hk : c.slot = c'.slot)
    (hw : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c.outerWord c.innerWord c.slot c.cuts =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c'.outerWord c'.innerWord c'.slot c'.cuts) : c = c' := by
  rcases c with ⟨outer, su, u, hu, inner, sv, v, hv, slot, cuts, hpos⟩
  rcases c' with ⟨outer', su', u', hu', inner', sv', v', hv', slot', cuts', hpos'⟩
  dsimp only at ho hi hk hw
  cases ho
  cases hi
  cases hk
  obtain ⟨heU, heV, heP⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.inputs_partition_unique u u' v v' slot cuts cuts' hpos hw
  cases heU
  cases heV
  have heCuts : cuts = cuts' := eq_of_heq heP
  cases heCuts
  have heSu := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_of_same_output outer outer su su' u.val hu hu'
  cases heSu
  have heSv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_of_same_output inner inner sv sv' v.val hv hv'
  cases heSv
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：実際の非退化 shuffle 成功は元の経路・Schedule を戻す入力データを一意に持つ（BF §1.5.8–9）。
方針：両基底語・分割・両成功 Schedule を構成し、正方向の経路と fusedSchedule の一致を証明する。
規約：正の内側 arity。経路・Schedule の一致や元の成功二表は仮定しない。
使われ方：TR 部分合成の全成功項の対応の逆方向と両方向の一意性。 -/
lemma shuffle_reconstruction_existsUnique {m n d e : ℕ} (hn : 0 < n) (k : Fin (m + 1))
    (s : ShufflePath d e) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n k (outer (s.horizontal j))
      (inner (s.vertical j))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃! c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e,
      c.outer = outer ∧ c.inner = inner ∧ c.slot = k ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts = s ∧ c.fusedSchedule = r ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c.outerWord c.innerWord c.slot c.cuts = out := by
  obtain ⟨u, v, ⟨p, hp, _⟩, _, _, ⟨su, hsu, _⟩, ⟨sv, hsv, _⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_source_partition hn k s outer inner r out h hc
  let c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e :=
    ⟨outer, su, u, hsu, inner, sv, v, hsv, k, p, by omega⟩
  have hpath : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts = s :=
    c.compositionPath_eq_of_success s r out h hc hp
  have hsched : c.fusedSchedule = r := c.fusedSchedule_eq_of_success s r out h hp
  refine ⟨c, ⟨rfl, rfl, rfl, hpath, hsched, hp⟩, ?_⟩
  intro c' hc'
  exact c'.eq_of_same_output c hc'.1 hc'.2.1 hc'.2.2.1 (hc'.2.2.2.2.2.trans hp.symm)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
