module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Rows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListGenerators
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
模型。文献の定義との比較は後で
# 置換列上の一般の table reduction

概要：Berger–Fresse §1.3.1 の table reduction を行長の有限和で定義する。
方針：正の行長の総和を n+d とし、行を連結して全射語の元へ送る。
規約：BE の置換は逆置換の一行表示で読む。arity 0 は空語を明示して扱う。
使われ方：正規化 BE 基底上の線形写像と鎖写像性の証明の入力となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：正の行長の選択全体（BF §1.3.1）。
方針：各行長を n 以下の有限添字とし、総和で次数を指定する。
規約：n=0 の分岐はこの添字集合を使わず別に定義する。
使われ方：TR の有限和の添字となる。 -/
abbrev Schedule (n d : ℕ) :=
  {r : Fin (d + 1) → Fin (n + 1) //
    (∀ i, 0 < (r i).val) ∧ (∑ i, (r i).val) = n + d}

/-- 概要：置換列と行長をリストの行へ直す（BF §1.3.1）。
方針：頂点の逆置換の一行表示と行長の組を順に並べる。
規約：逆置換は既存 BE の右乗法と値の左置換を整合させる。
使われ方：抽出処理 reduceRows の入力を供給する。 -/
def rows {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    List (List (Fin n) × ℕ) :=
  List.ofFn (fun i => (List.ofFn (fun j => (w i)⁻¹ j), (r.val i).val))

/-- 概要：table の指定行長の和は n+d（BF §1.3.1）。
方針：有限リストの和を有限型上の和へ移す。
規約：行数は d+1。
使われ方：抽出に成功した文字列の長さを固定する。 -/
lemma rows_sum {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map Prod.snd).sum = n + d := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using r.property.2

/-- 概要：行の抽出に成功した出力の長さは n+d（BF §1.3.1）。
方針：一般の抽出の長さ公式と行長の総和を合成する。
規約：無効な行長の選択について存在は主張しない。
使われ方：出力の長さの検査が成功することを保証する。 -/
lemma output_length {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    out.length = n + d := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_length _ _ _ h).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_sum w r)

variable (A : Type u) [CommRing A]

/-- 概要：一つの行長の選択が与える TR の項（BF §1.3.1）。
方針：抽出失敗なら零、成功なら連結された語を正規化する。
規約：退化語・非全射語も正規化によって零となる。
使われ方：全行長にわたる正符号の有限和の被加数。 -/
def term {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) []).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A)).getD 0

/-- 概要：任意の置換列に対する table reduction の有限和（BF §1.3.1）。
方針：全ての行長の選択の項を正符号で足す。
規約：arity 0 の次数零は空語、それ以外の nullary 成分は零。
使われ方：正規化 BE の自由基底上に線形写像を定める。 -/
def onSequence {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  if n = 0 then if d = 0 then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A [] else 0
  else ∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A w r

/-- 概要：BE の右作用は table の各行で値の左置換になる（BF §1.3.6）。
方針：積の逆元とリストの写像の式を使う。
規約：右から σ⁻¹ を掛ける共変な作用。
使われ方：TR の置換同変性の行の比較となる。 -/
lemma rows_action {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => w i * σ⁻¹) r =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map (fun p => (p.1.map σ, p.2)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn]
  congr 1
  funext i
  congr 1
  simp only [List.map_ofFn]
  congr 1

/-- 概要：一つの table 項は置換作用と両立する（BF §1.3.6）。
方針：行抽出とリスト正規化の同変性を合成する。
規約：無効な行長の選択も含む。
使われ方：TR の有限和の同変性を与える。 -/
lemma term_action {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun i => w i * σ⁻¹) r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A w r) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_action]
  have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_map σ σ.injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) []
  simp only [List.map_nil] at hm
  rw [hm]
  cases h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] with
  | none => simp
  | some out =>
    simp only [Option.map_some, Option.getD_some]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_listGenerator A σ out).symm

/-- 概要：一般の table reduction の和は対称群作用と両立（BF §1.3.6）。
方針：零 arity の分岐と各有限和の項の同変性を比較する。
規約：まだ微分保存やオペラッド射性は主張しない。
使われ方：χ の対称列への次数ごとの線形写像を構成する。 -/
lemma onSequence_action {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun i => w i * σ⁻¹) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence
  split
  · split
    · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_listGenerator A σ []).symm
    · exact (map_zero _).symm
  · simp only [map_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term_action]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
