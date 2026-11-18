module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.InnerRecurrentRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentBudget
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOfTable
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOutputUniqueness

/-!
模型。文献の定義との比較は後で
# 実際の shuffle 成功から元の内側 Schedule を復元

概要：Berger–Fresse §1.5.8 の逆構成で本来の内側次数の成功 Schedule を構成する。
方針：全内側復元の行末再出現と全射性から余剰総和を固定し、元の行列・行数を使う。
規約：正の内側 arity。元の内側成功や行長総和を追加仮定にしない。
使われ方：元の成功二表の逆構成と TR の全部分合成項の全単射。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：実際の非退化な成功 shuffle 表から元の内側次数の成功 Schedule を得る（BF §1.5.8）。
方針：行末再出現を復元表へ移し、全射性による余剰 n−1 と元の行数 e+1 を合わせる。
規約：元の内側表の成功も総和条件も仮定せず、合成 Schedule の成功だけから構成する。
使われ方：元の成功二表の内側を本来の TR の実際の一項として逆構成する。 -/
lemma shuffle_inner_schedule {m n d e : ℕ} (hn : 0 < n) (k : Fin (m + 1))
    (s : ShufflePath d e) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ innerSchedule : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n e,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows inner innerSchedule) [] = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out) ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out).IsChain (· ≠ ·) ∧ ∀ a : Fin n, a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out := by
  have hcover := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_covers _ r out h
  have hne : out.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ [] := by
    let a : Fin n := ⟨0, hn⟩
    have hm : a ∈ out.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) :=
      List.mem_filterMap.mpr ⟨_, hcover (insertedPosition m n k a), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_inserted k a⟩
    exact List.ne_nil_of_mem hm
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r)) [] = some out := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries_rows]
    exact h
  have hrec : ∀ picked, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r)) []
      picked → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked := by
    intro picked hp
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries_rows] at hp
    exact hp.recurrent_of_schedule _ r
  obtain ⟨table, picked, ht, hmatrix, hflat, hrecur⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.inner_recurrent_table_success k
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) [] out hs hc (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries_axis s outer inner r)
    hne hrec
  simp only [List.filterMap_nil] at ht
  have hinner := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_inner_isChain_of_success k s outer inner r out h hc
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries, List.map_ofFn, Function.comp_def] at hmatrix
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.collapse_vertical_ofFn s inner, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ hinner,
    List.map_ofFn] at hmatrix
  have hlen : table.length = e + 1 := by
    simpa only [List.length_map, List.length_ofFn] using congrArg List.length hmatrix
  have hnRows : ∀ p ∈ table, p.1.Nodup := by
    intro p hp
    have hm : p.1 ∈ table.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [hmatrix] at hm
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
    rw [← hj]
    exact List.nodup_ofFn_ofInjective (inner j).symm.injective
  have hexcess := ht.recurrent_excess hnRows hrecur
  rw [hflat, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dedup_length_of_coverage _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord_covers k out hcover)] at hexcess
  have hbounds := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_row_bounds table [] picked.flatten ht.reduceRows
  have hpos : ∀ x ∈ table.map Prod.snd, 0 < x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hbounds p hp).1
  have hsum := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_sub_one_add_length (table.map Prod.snd) hpos
  simp only [List.map_map, List.length_map, Function.comp_def] at hsum
  rw [hexcess, hlen] at hsum
  have htotal : (table.map Prod.snd).sum = n + e := by omega
  have hsuccess : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows table [] = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out) := by
    rw [← hflat]
    exact ht.reduceRows
  obtain ⟨innerSchedule, heq⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_of_table inner table (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out)
    hsuccess hmatrix htotal
  refine ⟨innerSchedule, ?_, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_isChain _, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord_covers k out hcover⟩
  rw [heq]
  exact hsuccess

/-- 概要：実際の成功から元の内側次数の基底語と一意な成功 Schedule を復元する（BF §1.5.8）。
方針：復元 Schedule の長さ・全射性・非退化性で基底語を作り、出力による一意性を使う。
規約：語は合成出力だけの内側復元に一致し、元の内側置換列での成功を返す。
使われ方：元の成功二表の逆構成と全項の一意な対応の内側部分。 -/
lemma shuffle_inner_basis {m n d e : ℕ} (hn : 0 < n) (k : Fin (m + 1))
    (s : ShufflePath d e) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e, List.ofFn v.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out ∧
      ∃! innerSchedule : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n e,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows inner innerSchedule) [] = some (List.ofFn v.val) := by
  obtain ⟨innerSchedule, hs, hchain, hcover⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_inner_schedule hn k s outer inner r out h hc
  have hlen : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out).length = n + e := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length inner innerSchedule _ hs
  let w : Fin (n + e) → Fin n := fun i => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out)[i.val]'(by rw [hlen]; exact i.isLt)
  have hw : List.ofFn w = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  have hsurj : Function.Surjective w := by
    intro a
    have ha : a ∈ List.ofFn w := by rw [hw]; exact hcover a
    exact List.mem_ofFn.mp ha
  have hnondeg : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate w := by
    have hcv : (List.ofFn w).IsChain (· ≠ ·) := by rw [hw]; exact hchain
    intro i j hij
    have hb : i.val + 1 < n + e := by omega
    have hne := List.isChain_ofFn.mp hcv i.val hb
    change w i ≠ w ⟨i.val + 1, hb⟩ at hne
    have he : (⟨i.val + 1, hb⟩ : Fin (n + e)) = j := Fin.ext hij
    simpa only [he] using hne
  let v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e := ⟨w, hsurj, hnondeg⟩
  have hsuccess : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows inner innerSchedule) [] = some (List.ofFn v.val) := by
    rw [hw]
    exact hs
  refine ⟨v, hw, innerSchedule, hsuccess, ?_⟩
  intro r' hr'
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_of_same_output inner inner r' innerSchedule v.val hr' hsuccess

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
