module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SplitPartsProperties
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartitionOfRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterScheduleRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.InnerScheduleRecovery

/-!
模型。文献の定義との比較は後で
# 実際の shuffle 成功から元の分割と合成語を復元

概要：Berger–Fresse §1.5.8–9 の逆構成で両復元語長から分割添字と合成語一致を構成する。
方針：全 splitParts の代入表示で長さを数え、最大境界損失から一意な重なり分割を得る。
規約：元の分割や共有端点は仮定しない。経路の往復と全項の和の対応は後続。
使われ方：任意の実際の shuffle 成功項から元の両成功 Schedule と分割を逆構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：正しい次数の両復元語を持つ非退化出力は一意な分割による合成語（BF §1.5.8–9）。
方針：代入長と両語長で splitParts の長さを飽和させ、既存分割の全 segment 一致を使う。
規約：共有端点や元の分割を追加仮定にしない。
使われ方：実際の成功 shuffle 項の元の分割を逆構成する。 -/
lemma recovered_partition_existsUnique {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (out : List (Fin (m + n))) (hc : out.IsChain (· ≠ ·))
    (hlen : out.length = (m + n) + (d + e))
    (hu : List.ofFn u.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) (hv : List.ofFn v.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out) :
    ∃! p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k p = out := by
  let parts := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) out
  obtain ⟨hcount, hn, hparts, hsub⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts_properties k out hc
  change parts.length = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).count k at hcount
  change out = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) parts at hsub
  have hcnt : parts.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k := by
    rw [← hu] at hcount
    exact hcount
  have hinner : out.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) = parts.flatten :=
    (congrArg (List.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) hsub).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.inner_substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) parts hcount)
  have hword : List.ofFn v.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten := by
    rw [hv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord, hinner]
  have houterLength : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).length = (m + 1) + d := by rw [← hu, List.length_ofFn]
  have hbalance := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_length k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) parts hcount
  rw [← hsub, ← hcount, hlen, houterLength] at hbalance
  have hsat : parts.flatten.length + 1 = (n + e) + parts.length := by omega
  have hex := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.exists_of_rows parts hparts hn v.val hword hsat
  rw [hcnt] at hex
  obtain ⟨p, hp⟩ := hex
  have hcompose : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k p = out := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord, hp, hu]
    exact hsub.symm
  refine ⟨p, hcompose, ?_⟩
  intro p' hp'
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.partition_unique u v k p' p (hp'.trans hcompose.symm)

/-- 概要：実際の非退化 shuffle 成功から元の両基底語・分割・一意な成功 Schedule を得る（BF §1.5.8）。
方針：両入力の本来の次数の復元に、実際の出力長による一意な分割構成を接続する。
規約：正の内側 arity。合成語一致までを返し、元の経路の復元一致はまだ主張しない。
使われ方：TR の全部分合成保存の全単射を作る逆方向の元データ。 -/
lemma shuffle_source_partition {m n d e : ℕ} (hn : 0 < n) (k : Fin (m + 1))
    (s : ShufflePath d e) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d, ∃ v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e,
      (∃! p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k p = out) ∧
      List.ofFn u.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out ∧ List.ofFn v.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out ∧
      (∃! su : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows outer su) [] = some (List.ofFn u.val)) ∧
      (∃! sv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n e, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows inner sv) [] = some (List.ofFn v.val)) := by
  obtain ⟨u, hu, hsu⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_outer_basis hn k s outer inner r out h hc
  obtain ⟨v, hv, hsv⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_inner_basis hn k s outer inner r out h hc
  exact ⟨u, v, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recovered_partition_existsUnique u v k out hc (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length _ r out h) hu hv,
    hu, hv, hsu, hsv⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
