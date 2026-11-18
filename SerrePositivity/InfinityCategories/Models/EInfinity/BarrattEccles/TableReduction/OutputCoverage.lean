module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-!
模型。文献の定義との比較は後で
# 成功 Schedule の出力の全射性

概要：Berger–Fresse §1.3.1 の成功した Schedule の出力が全てのラベルを含むことを示す。
方針：語長 n+d と重複除去の損失の上限 d から、異なる文字の個数が n と一致する。
規約：出力の非退化性を要求しない。
使われ方：合成語から復元する元の外側語の全射性を保証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：Fin n の語の異なる文字が n 個なら全ラベルを含む（BF §1.5.8）。
方針：重複除去長を toFinset の濃度に移し、全体集合との一致を使う。
規約：n=0 も含む。
使われ方：語長による飽和から実際の全射性を得る。 -/
lemma coverage_of_dedup_length {n : ℕ} (xs : List (Fin n)) (h : xs.dedup.length = n) :
    ∀ a : Fin n, a ∈ xs := by
  have hc : xs.toFinset.card = Fintype.card (Fin n) := by
    rw [List.card_toFinset, Fintype.card_fin, h]
  have he : xs.toFinset = Finset.univ := (Finset.card_eq_iff_eq_univ _).mp hc
  intro a
  have hm : a ∈ xs.toFinset := by rw [he]; exact Finset.mem_univ a
  exact List.mem_toFinset.mp hm

/-- 概要：全ラベルを含む Fin n の語の重複除去長は n（BF §1.5.8）。
方針：語の値集合を全体集合に一致させて濃度を取る。
規約：語の順序と重複数には依存しない。
使われ方：復元外側語の全射性から行長の計数へ進む。 -/
lemma dedup_length_of_coverage {n : ℕ} (xs : List (Fin n)) (h : ∀ a : Fin n, a ∈ xs) :
    xs.dedup.length = n := by
  have he : xs.toFinset = Finset.univ := by
    ext a
    simp only [List.mem_toFinset, h a, Finset.mem_univ]
  have hc := congrArg Finset.card he
  simpa only [List.card_toFinset, Finset.card_univ, Fintype.card_fin] using hc

/-- 概要：成功した一般の TR Schedule の出力は全てのラベルを含む（BF §1.3.1）。
方針：各行末だけが重複除去で失われる上界と n+d の全長から濃度の等号を強制する。
規約：任意の元の置換列と成功 Schedule に適用する。
使われ方：shuffle 合成表の出力の全射性を逆構成へ渡す。 -/
lemma output_covers {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    ∀ a : Fin n, a ∈ out := by
  obtain ⟨picked, he, hs, hn, hl, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.separatedRows_of_reduction w r out h
  have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.separatedRows_length_le picked hs hn
  have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dedup_length_le_arity out
  have hlen := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h
  rw [he, hl, Nat.add_sub_cancel] at hb
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.coverage_of_dedup_length out
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
