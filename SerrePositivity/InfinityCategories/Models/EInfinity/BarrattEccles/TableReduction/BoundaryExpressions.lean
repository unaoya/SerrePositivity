module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RawListDifferential
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NormalizedMap

/-!
模型。文献の定義との比較は後で
# Table reduction の微分保存の両辺の有限和

概要：Berger–Fresse §1.4.4 の微分保存を table 出力の削除和と頂点境界へ帰着する。
方針：正規化と削除の両立、BE の正規化生成元の交代境界を使う。
規約：両辺の一致をここでは仮定も主張もせず、それぞれの計算式を構成する。
使われ方：一文字だけの行と残りの相殺対を比較する組合せ的証明の対象となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：TR の一項の微分は抽出リストの符号付き削除和（BF §1.4.4）。
方針：抽出の成功・失敗で分岐し、リストの正規化との両立を使う。
規約：入力の単体次数は d+1。
使われ方：微分を行長の有限和の中へ移す。 -/
lemma differential_term {n d : ℕ} (w : Fin (d + 1 + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A w r) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) []).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential A)).getD 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term
  cases h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] with
  | none => exact map_zero _
  | some out =>
    simp only [Option.map_some, Option.getD_some]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential_listGenerator A out

/-- 概要：TR の微分は全 table 出力の削除和（BF §1.4.4）。
方針：線形写像を Schedule の有限和へ分配する。
規約：nullary 分岐の微分は零。
使われ方：削除項の対応と相殺を証明する有限和を与える。 -/
lemma differential_onSequence {n d : ℕ} (w : Fin (d + 1 + 1) → Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w) =
      if n = 0 then 0 else ∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1),
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) []).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential A)).getD 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence
  split
  · simp
  · simp only [map_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.differential_term]

/-- 概要：頂点を一つずつ削除した TR の交代和（BF §1.4.4）。
方針：削除位置を飛ばす有限添字で頂点列を前合成する。
規約：符号は頂点の番号に対する (−1)^i。
使われ方：table 出力の削除和と比較するもう一方の式。 -/
def vertexBoundary {n d : ℕ} (w : Fin (d + 1 + 1) → Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  ∑ i : Fin (d + 2), (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun j => w (i.succAbove j))

/-- 概要：BE 生成元の微分の TR は頂点境界の交代和（BF §1.4.4）。
方針：既存の交代境界の式と全生成元での TR の式を合わせる。
規約：退化する面も式の中へ含める。
使われ方：微分保存を二つの有限和の同一性に帰着する。 -/
lemma normalizedMap_d_generator (n d : ℕ)
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.simplicial n) _⦋d + 1⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 1) d
        (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n (d + 1) x)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A (_root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n (d + 1) x) := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator_d]
  simp only [map_sum, map_zsmul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_generator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary]
  apply Finset.sum_congr rfl
  intro i _
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
