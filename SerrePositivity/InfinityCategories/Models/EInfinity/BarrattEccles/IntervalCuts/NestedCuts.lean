module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositionSlotGeometry
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TwoPiecePartitions

/-!
模型。文献の定義との比較は後で
# 二段辺切断の有限添字と合成分割

概要：Berger–Fresse §2.2.6 の外側辺切断の指定出力に内側作用を施す非零項を表す。
方針：辺出力では内側の非零辺切断を選び、頂点出力では零語次数に限る。
規約：内側 arity 零を含み、存在しない辺切断は空の有限添字となる。
使われ方：部分合成の全切断添字への対応と出力・符号の照合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：二段辺切断の位置対が非零項を与える条件（BF §2.2.6）。
方針：外側切断の非退化性と内側の辺・頂点の分岐条件を持つ。
規約：none は非辺出力かつ零語次数、some は内側の非零辺切断。
使われ方：有限添字の部分型と計算可能な所属判定。 -/
def NestedEdgeCutValid {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (a : Fin (m + 1 + d) × Option (Fin (n + e))) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val a.1 ∧
    match a.2 with
    | some q => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.1 k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val q
    | none => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.1 k ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge ∧ e = 0

/-- 概要：二段辺切断の非零性は有限に判定できる（BF §2.2.6）。
方針：内側の切断点の none・some を分け、各非退化性と次数の等式を判定する。
規約：非計算的な選択を使わない。
使われ方：二段切断の有限和の実際の添字を列挙する。 -/
instance decidableNestedEdgeCutValid {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1)) : DecidablePred (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCutValid u v k) := by
  rintro ⟨p, q⟩
  cases q <;> unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCutValid <;> infer_instance

/-- 概要：二段に作用したときの非零辺切断の有限添字（BF §2.2.6）。
方針：外側切断点と、内側が辺ならその切断点、頂点なら none を持つ。
規約：none は内側語次数零かつ指定出力が頂点の場合に限る。
使われ方：部分合成の右辺を一つの有限和で表す。 -/
abbrev NestedEdgeCut {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) :=
  {a : Fin (m + 1 + d) × Option (Fin (n + e)) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCutValid u v k a}

namespace NestedEdgeCut

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

/-- 概要：外側の頂点出力へ零語次数の内側作用を施す二段切断（BF §2.2.6）。
方針：内側辺切断点を none として非辺条件と次数零を記録する。
規約：内側 arity 零も許す。
使われ方：頂点分岐の非零項を有限添字へ入れる。 -/
def ofVertex (p : Fin (m + 1 + d)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p)
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) (he : e = 0) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k :=
  ⟨(p, none), h, hk, he⟩

/-- 概要：外側の辺出力へ内側の非零辺切断を施す二段切断（BF §2.2.6）。
方針：内外の切断点と指定出力の辺条件を記録する。
規約：内側語の arity と次数は切断の存在だけで制限される。
使われ方：辺分岐の非零項を有限添字へ入れる。 -/
def ofEdge (p : Fin (m + 1 + d)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p)
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) (q : Fin (n + e)) (hq : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k := ⟨(p, some q), h, hk, hq⟩

/-- 概要：二段切断の指定色は一回か二回だけ出現（BF §2.2.1）。
方針：外側切断の左右単射性から出現数上限を取り、全射性で零を除く。
規約：内側作用の二つの分岐に依存しない。
使われ方：合成の分割を一部分か二部分へ限定する。 -/
lemma occurrenceCount_eq_one_or_two (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1 ∨ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 2 := by
  have hle := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceCount_le_two_of_cut u.val a.val.1 a.property.1 k
  have hpos := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k
  omega

/-- 概要：内側が頂点へ作用すると指定色は一出現（BF §2.2.6）。
方針：none の非辺条件を非切断点の一出現分類へ送る。
規約：none の場合の内側語次数は定義により零。
使われ方：唯一の全語分割を選ぶ。 -/
lemma occurrenceCount_eq_one_of_none (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (ha : a.val.2 = none) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1 := by
  have h := a.property.2
  rw [ha] at h
  exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_ne_edge_iff_single_nonpivot u a.val.1 a.property.1 k).mp h.1).2

/-- 概要：内側が辺へ作用し切断点色と異なれば指定色は二出現（BF §2.2.6）。
方針：辺出力の分類で切断点色の分岐を除く。
規約：内側切断点の非退化性を保持する。
使われ方：内側の切断点から二部分割を作る。 -/
lemma occurrenceCount_eq_two_of_some_nonpivot (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hk : k ≠ u.val a.val.1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 2 := by
  have h := a.property.2
  rw [ha] at h
  exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff_pivot_or_two u a.val.1 a.property.1 k).mp h.1).resolve_left hk

/-- 概要：二段切断に対応する実際の内側語の重なる分割（BF §1.2.4・§2.2.6）。
方針：一出現なら全語、二出現なら内側辺切断点で二分する。
規約：頂点分岐では空の内側語の唯一分割も同じ定義で扱う。
使われ方：二段切断から部分合成の分割添字を構成する。 -/
def partition (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e) :=
  match ha : a.val.2 with
  | none => cast (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e))
      (a.occurrenceCount_eq_one_of_none ha).symm) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single (n + e))
  | some q =>
    if hk : k = u.val a.val.1 then
      cast (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e))
        (by rw [hk]; exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceCount_pivot_eq_one u a.val.1 a.property.1).symm))
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single (n + e))
    else cast (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e))
      (a.occurrenceCount_eq_two_of_some_nonpivot q ha hk).symm) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q)

/-- 概要：頂点分岐で選んだ分割を一部分へ移すと全語の唯一分割（BF §1.2.4）。
方針：分割の構成を評価して互いに逆の個数移送を打ち消す。
規約：空の内側語も同時に扱う。
使われ方：対応した合成項の分割を実際の唯一分割へ同定する。 -/
lemma partition_of_none (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (ha : a.val.2 = none) :
    cast (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e))
      (a.occurrenceCount_eq_one_of_none ha)) a.partition = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single (n + e) := by
  rcases a with ⟨⟨p, q⟩, h⟩
  cases q with
  | none => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.partition]
  | some q => cases ha

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
