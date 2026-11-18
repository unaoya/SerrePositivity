module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ShuffleSourceNondegenerate
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterWordCoverage
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentBudget
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOfTable
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOutputUniqueness

/-!
模型。文献の定義との比較は後で
# 実際の shuffle 成功から元の外側 Schedule を復元

概要：Berger–Fresse §1.5.8 の逆構成で、元の外側次数の本来の Schedule を構成する。
方針：全射性と行末再出現で行長−1 総和を固定し、圧縮の保存と正しい行数を使う。
規約：正の内側 arity。行長総和や元の外側成功は追加仮定にしない。
使われ方：一般の TR 部分合成保存で元の成功二表の外側を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：圧縮外側表の行長−1 総和は元の外側 arity−1（BF §1.5.8）。
方針：元の Schedule の行末再出現と全射性を外側へ移し、圧縮の総和保存を使う。
規約：この総和計算自体には出力の非退化性を要求しない。
使われ方：元の外側次数の Schedule の行長総和条件を得る。 -/
lemma shuffle_outer_excess {m n d e : ℕ} (hn : 0 < n) (k : Fin (m + 1))
    (s : ShufflePath d e) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out)
    (picked : List (List (Fin (m + n)))) (finish : List (Fin (m + n)))
    (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r)) [] picked finish)
    (ho : out = picked.flatten) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked)).map
      (fun p => p.2 - 1)).sum = m := by
  let w := fun i => permutationComposition m n k (outer (s.horizontal i)) (inner (s.vertical i))
  have hp' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] picked finish := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries_rows] using hp
  have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] picked :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_lengths _ _ _
      (by simpa only [List.append_nil] using hp'.append [] [] rfl) hp'.lengths
  have hl : picked.length = d + e + 1 := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn] using ht.length
  have hlen : picked.flatten.length = (m + n) + (d + e) := by
    rw [← ho]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h
  have hrec : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_of_length picked
    (ht.separatedRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_nodup w r)) ht.nonempty (by rw [hl, Nat.add_sub_cancel]; exact hlen)
  have htOuter := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable_trace k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r)
    [] finish picked hp
  have hcoverage : ∀ a : Fin (m + 1), a ∈ (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)).flatten := by
    intro a
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_outer_picked k a picked).mpr
    rw [← ho]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_covers hn k out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_covers w r out h) a
  have hbefore := htOuter.recurrent_excess
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable_rows_nodup k _ picked) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recurrentEnds_outerWord k picked hrec)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dedup_length_of_coverage _ hcoverage, Nat.add_sub_cancel] at hbefore
  have hbounds := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_row_bounds _ _ _ htOuter.reduceRows
  have hpos : ∀ p ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked,
      0 < p.2 := fun p hp => (hbounds p hp).1
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows_positive_excess _ hpos).2.trans hbefore

/-- 概要：実際の非退化な成功 shuffle 表から元の外側次数の成功 Schedule を得る（BF §1.5.8）。
方針：復元外側表の正しい行列・行数に余剰総和を加え、Schedule の全条件を証明する。
規約：元の外側表の成功や総和を仮定せず、元の合成 Schedule の成功だけから構成する。
使われ方：元の成功二表の外側を元の TR の実際の一項として逆構成する。 -/
lemma shuffle_outer_schedule {m n d e : ℕ} (hn : 0 < n) (k : Fin (m + 1))
    (s : ShufflePath d e) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ outerSchedule : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows outer outerSchedule) [] = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).IsChain (· ≠ ·) ∧ ∀ a : Fin (m + 1), a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out := by
  obtain ⟨picked, finish, hp, ho, hs, hchain, hrows, hlen⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_outer_recovery_with_rows hn k s outer inner r out h hc
  let table := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked)
  have hbounds := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_row_bounds table [] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) hs
  have hpos : ∀ x ∈ table.map Prod.snd, 0 < x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hbounds p hp).1
  have hsum := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_sub_one_add_length (table.map Prod.snd) hpos
  simp only [List.map_map, List.length_map, Function.comp_def] at hsum
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_outer_excess hn k s outer inner r out h picked finish hp ho
  change (table.map (fun p => p.2 - 1)).sum = m at he
  change table.length = d + 1 at hlen
  rw [he, hlen] at hsum
  have htotal : (table.map Prod.snd).sum = (m + 1) + d := by omega
  obtain ⟨outerSchedule, heq⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_of_table outer table (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) hs hrows htotal
  refine ⟨outerSchedule, ?_, hchain, ?_⟩
  · rw [heq]
    exact hs
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_covers hn k out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_covers _ r out h)

/-- 概要：実際の成功から元の外側次数の基底語と一意な成功 Schedule を復元する（BF §1.5.8）。
方針：復元 Schedule の成功長・全射性・非退化性で基底語を作り、出力による一意性を使う。
規約：語は合成出力だけの外側復元に一致し、元の外側置換列での成功を返す。
使われ方：元の成功二表の逆構成と全項の一意な対応の外側部分。 -/
lemma shuffle_outer_basis {m n d e : ℕ} (hn : 0 < n) (k : Fin (m + 1))
    (s : ShufflePath d e) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d, List.ofFn u.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out ∧
      ∃! outerSchedule : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows outer outerSchedule) [] = some (List.ofFn u.val) := by
  obtain ⟨outerSchedule, hs, hchain, hcover⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_outer_schedule hn k s outer inner r out h hc
  have hlen : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).length = (m + 1) + d := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length outer outerSchedule _ hs
  let v : Fin ((m + 1) + d) → Fin (m + 1) := fun i =>
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out)[i.val]'(by rw [hlen]; exact i.isLt)
  have hv : List.ofFn v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  have hsurj : Function.Surjective v := by
    intro a
    have ha : a ∈ List.ofFn v := by rw [hv]; exact hcover a
    exact List.mem_ofFn.mp ha
  have hnondeg : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v := by
    have hcv : (List.ofFn v).IsChain (· ≠ ·) := by rw [hv]; exact hchain
    intro i j hij
    have hb : i.val + 1 < (m + 1) + d := by omega
    have hne := List.isChain_ofFn.mp hcv i.val hb
    change v i ≠ v ⟨i.val + 1, hb⟩ at hne
    have he : (⟨i.val + 1, hb⟩ : Fin ((m + 1) + d)) = j := Fin.ext hij
    simpa only [he] using hne
  let u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d := ⟨v, hsurj, hnondeg⟩
  have hsuccess : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows outer outerSchedule) [] = some (List.ofFn u.val) := by
    rw [hv]
    exact hs
  refine ⟨u, hv, outerSchedule, hsuccess, ?_⟩
  intro r' hr'
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_of_same_output outer outer r' outerSchedule u.val hr' hsuccess

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
