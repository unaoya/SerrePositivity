module

public import SerrePositivity.EInfinity.Surjection.SplitPartsProperties
public import SerrePositivity.EInfinity.Surjection.OverlapPartitionOfRows
public import SerrePositivity.EInfinity.Surjection.OuterScheduleRecovery
public import SerrePositivity.EInfinity.Surjection.InnerScheduleRecovery

/-!
# 実際の shuffle 成功から元の分割と合成語を復元

概要：Berger–Fresse §1.5.8–9 の逆構成で両復元語長から分割添字と合成語一致を構成する。
方針：全 splitParts の代入表示で長さを数え、最大境界損失から一意な重なり分割を得る。
規約：元の分割や共有端点は仮定しない。経路の往復と全項の和の対応は後続。
使われ方：任意の実際の shuffle 成功項から元の両成功 Schedule と分割を逆構成する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection.CompositeRecovery

open BarrattEccles TableReduction

/-- 概要：正しい次数の両復元語を持つ非退化出力は一意な分割による合成語（BF §1.5.8–9）。
方針：代入長と両語長で splitParts の長さを飽和させ、既存分割の全 segment 一致を使う。
規約：共有端点や元の分割を追加仮定にしない。
使われ方：実際の成功 shuffle 項の元の分割を逆構成する。 -/
lemma recovered_partition_existsUnique {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (out : List (Fin (m + n))) (hc : out.IsChain (· ≠ ·))
    (hlen : out.length = (m + n) + (d + e))
    (hu : List.ofFn u.val = outerWord k out) (hv : List.ofFn v.val = innerWord k out) :
    ∃! p : OverlapPartition (occurrenceCount u.val k) (n + e), compositeWord u v k p = out := by
  let parts := splitParts k (outerWord k out) out
  obtain ⟨hcount, hn, hparts, hsub⟩ := splitParts_properties k out hc
  change parts.length = (outerWord k out).count k at hcount
  change out = substitute k (outerWord k out) parts at hsub
  have hcnt : parts.length = occurrenceCount u.val k := by
    rw [← hu] at hcount
    exact hcount
  have hinner : out.filterMap (innerLabel k) = parts.flatten :=
    (congrArg (List.filterMap (innerLabel k)) hsub).trans
      (inner_substitute k (outerWord k out) parts hcount)
  have hword : List.ofFn v.val = AdjacentCollapse.collapse parts.flatten := by
    rw [hv, innerWord, hinner]
  have houterLength : (outerWord k out).length = (m + 1) + d := by rw [← hu, List.length_ofFn]
  have hbalance := substitute_length k (outerWord k out) parts hcount
  rw [← hsub, ← hcount, hlen, houterLength] at hbalance
  have hsat : parts.flatten.length + 1 = (n + e) + parts.length := by omega
  have hex := OverlapPartition.exists_of_rows parts hparts hn v.val hword hsat
  rw [hcnt] at hex
  obtain ⟨p, hp⟩ := hex
  have hcompose : compositeWord u v k p = out := by
    rw [compositeWord, hp, hu]
    exact hsub.symm
  refine ⟨p, hcompose, ?_⟩
  intro p' hp'
  exact partition_unique u v k p' p (hp'.trans hcompose.symm)

/-- 概要：実際の非退化 shuffle 成功から元の両基底語・分割・一意な成功 Schedule を得る（BF §1.5.8）。
方針：両入力の本来の次数の復元に、実際の出力長による一意な分割構成を接続する。
規約：正の内側 arity。合成語一致までを返し、元の経路の復元一致はまだ主張しない。
使われ方：TR の全部分合成保存の全単射を作る逆方向の元データ。 -/
lemma shuffle_source_partition {m n d e : ℕ} (hn : 0 < n) (k : Fin (m + 1))
    (s : ShufflePath d e) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : reduceRows (rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ u : BasisWord (m + 1) d, ∃ v : BasisWord n e,
      (∃! p : OverlapPartition (occurrenceCount u.val k) (n + e), compositeWord u v k p = out) ∧
      List.ofFn u.val = outerWord k out ∧ List.ofFn v.val = innerWord k out ∧
      (∃! su : Schedule (m + 1) d,
        reduceRows (rows outer su) [] = some (List.ofFn u.val)) ∧
      (∃! sv : Schedule n e, reduceRows (rows inner sv) [] = some (List.ofFn v.val)) := by
  obtain ⟨u, hu, hsu⟩ := shuffle_outer_basis hn k s outer inner r out h hc
  obtain ⟨v, hv, hsv⟩ := shuffle_inner_basis hn k s outer inner r out h hc
  exact ⟨u, v, recovered_partition_existsUnique u v k out hc (output_length _ r out h) hu hv,
    hu, hv, hsu, hsv⟩

end SerrePositivity.EInfinity.Surjection.CompositeRecovery
