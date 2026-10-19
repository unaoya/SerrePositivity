module

public import SerrePositivity.EInfinity.Surjection.InnerTableRecovery
public import SerrePositivity.EInfinity.Surjection.ShuffleSourceNondegenerate
public import SerrePositivity.EInfinity.Surjection.AdjacentCollapseMembership
public import SerrePositivity.EInfinity.TableReduction.OutputCoverage

/-!
# 実際の shuffle 成功から元の内側行列の成功を復元

概要：Berger–Fresse §1.5.8 の全内側表の逆構成を実際の shuffle 経路へ適用する。
方針：成功出力の全射性で射影非空性を得て、全水平区間を接続し、垂直座標の反復を除く。
規約：正の内側 arity。元の内側表の成功や行長総和は仮定しない。
使われ方：元の内側次数の成功 Schedule の行列・行数・全射非退化出力を供給する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection.CompositeRecovery

open BarrattEccles TableReduction

/-- 概要：復元内側語への所属は元の挿入ラベルへの所属と同値（BF §1.5.8）。
方針：縮約の所属保存と内側部分単射射影の逆像を使う。
規約：元の語の全射性や非退化性は要求しない。
使われ方：実際の合成出力の全射性を復元内側語へ移す。 -/
lemma mem_innerWord {m n : ℕ} (k : Fin (m + 1)) (a : Fin n)
    (xs : List (Fin (m + n))) :
    a ∈ innerWord k xs ↔ insertedPosition m n k a ∈ xs := by
  rw [innerWord, AdjacentCollapse.mem_collapse]
  constructor
  · intro ha
    obtain ⟨b, hb, hf⟩ := List.mem_filterMap.mp ha
    rwa [(innerLabel_eq_some_iff k b a).mp hf] at hb
  · intro ha
    exact List.mem_filterMap.mpr ⟨_, ha, innerLabel_inserted k a⟩

/-- 概要：全ラベルを含む合成語から復元した内側語も全ラベルを含む（BF §1.5.8）。
方針：指定内側値の実際の挿入ラベルを元の全射性で取り出す。
規約：零 arity も含む。
使われ方：復元内側基底語の全射性。 -/
lemma innerWord_covers {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + n)))
    (h : ∀ b : Fin (m + n), b ∈ xs) : ∀ a : Fin n, a ∈ innerWord k xs := by
  intro a
  exact (mem_innerWord k a xs).mpr (h _)

/-- 概要：実際の非退化 shuffle 成功から元の内側行列・行数の成功表を得る（BF §1.5.8）。
方針：全水平区間の接続に実際の軸条件を渡し、元の内側列の非退化性で縮約を除く。
規約：正の内側 arity。行長総和は後続で証明する。
使われ方：元の内側次数の本来の Schedule を逆構成する。 -/
lemma shuffle_inner_recovery_with_rows {m n d e : ℕ} (hn : 0 < n)
    (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : reduceRows (rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ table : List (List (Fin n) × ℕ),
      reduceRows table [] = some (innerWord k out) ∧ (innerWord k out).IsChain (· ≠ ·) ∧
      table.map Prod.fst = List.ofFn (fun j => List.ofFn (inner j).symm) ∧
      table.length = e + 1 ∧ ∀ a : Fin n, a ∈ innerWord k out := by
  have hcover := output_covers _ r out h
  have hne : out.filterMap (innerLabel k) ≠ [] := by
    let a : Fin n := ⟨0, hn⟩
    have hm : a ∈ out.filterMap (innerLabel k) :=
      List.mem_filterMap.mpr ⟨_, hcover (insertedPosition m n k a), innerLabel_inserted k a⟩
    exact List.ne_nil_of_mem hm
  have hs : reduceRows (mixedTable k (shuffleTableEntries s outer inner r)) [] = some out := by
    rw [shuffleTableEntries_rows]
    exact h
  obtain ⟨table, hmatrix, hsuccess⟩ := inner_table_success k
    (shuffleTableEntries s outer inner r) [] out hs hc (shuffleTableEntries_axis s outer inner r)
    hne
  have hinner := shuffle_inner_isChain_of_success k s outer inner r out h hc
  simp only [shuffleTableEntries, List.map_ofFn, Function.comp_def] at hmatrix
  rw [collapse_vertical_ofFn s inner, AdjacentCollapse.collapse_eq_self _ hinner,
    List.map_ofFn] at hmatrix
  have hlen : table.length = e + 1 := by
    simpa only [List.length_map, List.length_ofFn] using congrArg List.length hmatrix
  refine ⟨table, ?_, AdjacentCollapse.collapse_isChain _, hmatrix, hlen,
    innerWord_covers k out hcover⟩
  simpa only [List.filterMap_nil] using hsuccess

end SerrePositivity.EInfinity.Surjection.CompositeRecovery
