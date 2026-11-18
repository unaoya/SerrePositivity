module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapRowsReconstruction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapSegments

/-!
模型。文献の定義との比較は後で
# 長さが飽和した挿入部分語から実際の重なり分割を構成

概要：Berger–Fresse §1.5.8 の逆構成で、部分語列を既存の OverlapPartition の全 segment に戻す。
方針：各部分長を有限値へ包み、長さ飽和で総和を満たし、強制された共有端点で全区間を照合する。
規約：各部分語は非空非退化。共有端点は仮定せず長さから証明する。
使われ方：合成出力の最大挿入連続区間から元の分割を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：長さ飽和を持つ非空非退化な部分語列から重なり分割を作る（BF §1.5.8）。
方針：各部分長を全縮約語長以下と示し、元の部分長総和を分割の等式へ移す。
規約：元の部分語と全縮約語の長さだけから実際の有限分割添字を構成する。
使われ方：元の内側語に対する部分合成和の実際の添字を逆構成する。 -/
def ofRows (parts : List (List α))
    (hc : ∀ row ∈ parts, row.IsChain (· ≠ ·)) (hne : ∀ row ∈ parts, row ≠ [])
    (hsat : parts.flatten.length + 1 = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length + parts.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition parts.length (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length := by
  let r : Fin parts.length → Fin ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length + 1) := fun i =>
    ⟨(parts.get i).length, by
      have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.row_length_le_collapse_flatten parts hc (parts.get i) (List.get_mem parts i)
      omega⟩
  refine ⟨r, ?_, ?_⟩
  · intro i
    exact Or.inl (List.length_pos_iff.mpr (hne (parts.get i) (List.get_mem parts i)))
  · have he : List.ofFn (fun i => (r i).val) = parts.map List.length := by
      change List.ofFn (List.length ∘ parts.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [← List.sum_ofFn, he, ← List.length_flatten]
    exact hsat

/-- 概要：復元分割の各部分長は元の部分語長そのもの（BF §1.5.8）。
方針：構成した有限値の値を評価する。
規約：元の語の部分語の順番を保持する。
使われ方：元の部分長と分割添字の往復。 -/
lemma ofRows_val (parts : List (List α))
    (hc : ∀ row ∈ parts, row.IsChain (· ≠ ·)) (hne : ∀ row ∈ parts, row ≠ [])
    (hsat : parts.flatten.length + 1 = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length + parts.length)
    (i : Fin parts.length) : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.ofRows parts hc hne hsat).val i).val = (parts.get i).length := rfl

/-- 概要：復元分割の全 segment は元の全挿入部分語に一致する（BF §1.5.8）。
方針：長さ飽和で全共有端点を導き、累積部分長−1 での区間復元を適用する。
規約：v は全連結語の縮約を表す任意の有限列。端点一致を追加仮定にしない。
使われ方：復元した OverlapPartition による実際の合成語一致。 -/
lemma ofRows_segments (parts : List (List α))
    (hc : ∀ row ∈ parts, row.IsChain (· ≠ ·)) (hne : ∀ row ∈ parts, row ≠ [])
    (hsat : parts.flatten.length + 1 = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length + parts.length)
    (v : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length → α) (hv : List.ofFn v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.ofRows parts hc hne hsat).segments v = parts := by
  have hp : 0 < parts.length := by
    by_contra hh
    have he : parts = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [he, List.flatten_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, List.length_nil, Nat.zero_add] at hsat
    omega
  have he : parts.flatten.length = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length + (parts.length - 1) := by
    omega
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.shared_endpoints_of_saturated parts hc hne he
  let r := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.ofRows parts hc hne hsat
  have hsteps : List.ofFn (fun j => (r.val j).val - 1) =
      parts.map (fun row => row.length - 1) := by
    change List.ofFn ((fun row : List α => row.length - 1) ∘ parts.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  apply List.ext_getElem
  · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segments, List.length_ofFn]
  · intro i hi hj
    change (List.ofFn (r.segment v))[i]'(by simpa only [List.length_ofFn] using hj) = parts[i]
    rw [List.getElem_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment, hv]
    change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).drop
      ((List.ofFn (fun j => (r.val j).val - 1)).take i).sum).take (parts.get ⟨i, hj⟩).length = _
    rw [hsteps]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.shared_rows_take parts hc hne hs i hj

/-- 概要：指定した有限内側語に対し元の全部分語を持つ重なり分割が存在する（BF §1.5.8）。
方針：有限語長を全縮約語長へ一致させ、ofRows と全区間一致を適用する。
規約：内側語は任意の値型で、非退化性と共有端点は部分語と長さ飽和から得る。
使われ方：復元した元の内側 BasisWord の本来の長さで分割を構成する。 -/
lemma exists_of_rows {l : ℕ} (parts : List (List α))
    (hc : ∀ row ∈ parts, row.IsChain (· ≠ ·)) (hne : ∀ row ∈ parts, row ≠ [])
    (v : Fin l → α) (hv : List.ofFn v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten)
    (hsat : parts.flatten.length + 1 = l + parts.length) :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition parts.length l, r.segments v = parts := by
  have hl : l = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length := by
    simpa only [List.length_ofFn] using congrArg List.length hv
  subst l
  exact ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.ofRows parts hc hne hsat, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.ofRows_segments parts hc hne hsat v hv⟩

/-- 概要：指定した全部分語を持つ復元重なり分割は一意に存在する（BF §1.5.8–9）。
方針：構成の存在に加え、全 segment の長さが分割の有限値を一意に決めると使う。
規約：元の外側語や合成語の一意性を追加仮定にしない。
使われ方：合成項の逆構成で元の分割添字の一意性も同時に得る。 -/
lemma existsUnique_of_rows {l : ℕ} (parts : List (List α))
    (hc : ∀ row ∈ parts, row.IsChain (· ≠ ·)) (hne : ∀ row ∈ parts, row ≠ [])
    (v : Fin l → α) (hv : List.ofFn v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten)
    (hsat : parts.flatten.length + 1 = l + parts.length) :
    ∃! r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition parts.length l, r.segments v = parts := by
  obtain ⟨r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.exists_of_rows parts hc hne v hv hsat
  refine ⟨r, hr, ?_⟩
  intro r' hr'
  have he := congrArg (List.map List.length) (hr'.trans hr.symm)
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segments, List.map_ofFn, Function.comp_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment_length] at he
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun (List.ofFn_injective he) i)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition
