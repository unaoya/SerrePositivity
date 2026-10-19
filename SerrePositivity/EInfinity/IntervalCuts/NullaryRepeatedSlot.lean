module

public import SerrePositivity.EInfinity.IntervalCuts.CochainCompositionPositive
public import SerrePositivity.EInfinity.Surjection.NullaryErasure

/-!
# 反復する指定色への空語代入の辺零性

概要：Berger–Fresse §2.2.6・§3.1 の nullary 合成で一出現でない指定色を処理する。
方針：空語には辺切断がなく、頂点分岐は指定色の一出現を強制することを使う。
規約：零性は元の実際の複体射の両辺で証明する。
使われ方：nullary の辺部分合成則を唯一出現の削除語比較へ絞る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

namespace NestedEdgeCut

/-- 概要：空の内側語の二段切断は必ず頂点入力（BF §2.2.6）。
方針：辺切断位置が Fin 0 に入る分岐を排除する。
規約：外側語の全次数と全挿入位置。
使われ方：nullary の有限添字を指定色一出現に制限する。 -/
lemma nullary_eq_none {m d : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord 0 0}
    {i : Fin (m + 1)} (a : NestedEdgeCut u v i) : a.val.2 = none := by
  cases h : a.val.2 with
  | none => rfl
  | some q => exact Fin.elim0 q

/-- 概要：空語の非零二段辺切断の指定色は一出現（BF §2.2.6）。
方針：唯一可能な頂点分岐の出現数分類を使う。
規約：外側 arity・次数は任意。
使われ方：反復指定色の二段切断添字が空であること。 -/
lemma nullary_occurrenceCount {m d : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord 0 0}
    {i : Fin (m + 1)} (a : NestedEdgeCut u v i) : occurrenceCount u.val i = 1 :=
  a.occurrenceCount_eq_one_of_none a.nullary_eq_none

/-- 概要：空語の二段切断の指定出力は非辺（BF §2.2.6）。
方針：空の辺位置を排除して頂点分岐の条件を取り出す。
規約：全外側語次数。
使われ方：活動位置の色から指定色を除く。 -/
lemma nullary_slot_nonedge {m d : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord 0 0}
    {i : Fin (m + 1)} (a : NestedEdgeCut u v i) : edgeOutput u a.val.1 i ≠ edge := by
  have h := a.property.2
  rw [a.nullary_eq_none] at h
  exact h.1

/-- 概要：空語の二段切断の切断点色は指定色と異なる（BF §2.2.6）。
方針：非辺指定出力の一出現・非切断点分類を使う。
規約：全外側語次数。
使われ方：残り位置写像で実際の切断点を保持する。 -/
lemma nullary_pivot_ne_slot {m d : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord 0 0}
    {i : Fin (m + 1)} (a : NestedEdgeCut u v i) : u.val a.val.1 ≠ i :=
  ((edgeOutput_ne_edge_iff_single_nonpivot u a.val.1 a.property.1 i).mp
    a.nullary_slot_nonedge).1.symm

end NestedEdgeCut

variable (A : Type u) [CommRing A]

/-- 概要：一出現でない指定色への空語の二段辺作用は零（BF §3.1）。
方針：実際の右辺を二段切断有限和へ移し、空の添字型で和を消す。
規約：実際の整数複体射、全外側語次数。
使われ方：nullary 合成則の反復指定色分岐の右辺。 -/
lemma iteratedCochainAction_basis_edge_nullary_of_count_ne_one {m d : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord 0 0) (i : Fin (m + 1))
    (hi : occurrenceCount u.val i ≠ 1) :
    (iteratedCochainAction A m 0 i).f (-((d + 0 + 1 : ℕ) : ℤ))
      (wordPairEdgeInput A u v) = 0 := by
  let _ : IsEmpty (NestedEdgeCut u v i) := ⟨fun a => hi a.nullary_occurrenceCount⟩
  have H := iteratedCochainAction_basis_edge_nested_sum A u v i
    (-((d + 0 + 1 : ℕ) : ℤ)) (by omega)
  have hx := SerrePositivity.DifferentialGraded.nested_left_apply
    (complex A (m + 1)) (complex A 0) (interval A) (-(d : ℤ)) (-(0 : ℤ)) (-1)
    (-((d + 0 : ℕ) : ℤ)) (-((d + 0 + 1 : ℕ) : ℤ)) (by omega) (by omega)
    ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)))
    ((complexXIso A 0 0).inv (basis A 0 0 (ULift.up v))) (faceVector A edge)
  exact (congrArg (fun x => (iteratedCochainAction A m 0 i).f
    (-((d + 0 + 1 : ℕ) : ℤ)) x) hx).trans (H.trans (Fintype.sum_empty _))

/-- 概要：一出現でない指定色への空語の実際の合成辺作用は零（BF §2.2.6）。
方針：実際の左辺を語の部分合成へ戻し、空の合成分割の和を零にする。
規約：余代数の合成則は仮定しない。
使われ方：nullary 合成則の反復指定色分岐の左辺。 -/
lemma cochainAction_composition_basis_edge_nullary_of_count_ne_one {m d : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord 0 0) (i : Fin (m + 1))
    (hi : occurrenceCount u.val i ≠ 1) :
    ((complexPartialComposition A m 0 i ▷ interval A) ≫ cochainAction A (m + 0)).f
      (-((d + 0 + 1 : ℕ) : ℤ)) (wordPairEdgeInput A u v) = 0 := by
  exact (cochainAction_composition_basis_edge A u v i).trans (by
    rw [compositionOnWords_nullary_of_count_ne_one A u v i hi, map_zero])

/-- 概要：反復する指定色では nullary の辺部分合成則が成立（BF §2.2.6・§3.1）。
方針：実際の左右の零性を連結する。
規約：外側語次数と挿入位置は任意。
使われ方：nullary の残りを一出現色の削除語比較へ絞る。 -/
lemma cochainAction_composition_basis_edge_nullary_eq_iterated_of_count_ne_one {m d : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord 0 0) (i : Fin (m + 1))
    (hi : occurrenceCount u.val i ≠ 1) :
    ((complexPartialComposition A m 0 i ▷ interval A) ≫ cochainAction A (m + 0)).f
      (-((d + 0 + 1 : ℕ) : ℤ)) (wordPairEdgeInput A u v) =
        (iteratedCochainAction A m 0 i).f (-((d + 0 + 1 : ℕ) : ℤ))
          (wordPairEdgeInput A u v) :=
  (cochainAction_composition_basis_edge_nullary_of_count_ne_one A u v i hi).trans
    (iteratedCochainAction_basis_edge_nullary_of_count_ne_one A u v i hi).symm

end SerrePositivity.EInfinity.IntervalCuts
