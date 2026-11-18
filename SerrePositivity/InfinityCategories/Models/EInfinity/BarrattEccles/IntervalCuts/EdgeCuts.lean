module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesuras
public import Mathlib.Data.Fintype.Prod

/-!
模型。文献の定義との比較は後で
# Δ¹ の辺の区間切断

概要：Berger–Fresse §2.2.1–6 の区間切断を標準一単体の辺へ特殊化する。
方針：唯一の長さ一の区間を指定し、その位置の文字を二頂点へ複製する。
規約：位置は零始まり。各色の頂点列は元の位置順に連結する。
使われ方：Δ¹ 上の χ の余演算の非零項と符号を有限に計算する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：辺を含む切断区間の両端に零・一を配置する（BF §2.2.1）。
方針：複製前の位置 p 以下を零、それより後を一とする。
規約：展開後の位置数は l+1。
使われ方：各色へ集める正規化単体の頂点。 -/
def edgeVertex {l : ℕ} (p : Fin l) (q : Fin (l + 1)) : Fin 2 :=
  if q.val ≤ p.val then 0 else 1

/-- 概要：展開した辺の頂点列は単調（BF §2.2.1）。
方針：切断点以前は零、以後は一であることを使う。
規約：色を集める前の全頂点列について主張する。
使われ方：同じ色の重複がない条件を非退化単体の条件と結ぶ。 -/
lemma monotone_edgeVertex {l : ℕ} (p : Fin l) : Monotone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeVertex p) := by
  intro a b hab
  have hab' := Fin.le_def.mp hab
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeVertex]
  split_ifs <;> simp_all only [Fin.le_def] <;> omega

/-- 概要：辺の両端は同じ色を持つ（BF §2.2.1）。
方針：predAbove で位置 p を二回評価する。
規約：区間 p は [0,1]、他の区間は一点。
使われ方：全ての出力頂点列を同時に表す。 -/
def edgeLabel {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (q : Fin (l + 1)) : Fin n := u (p.predAbove q)

/-- 概要：展開した各頂点の色と値（BF §2.2.1）。
方針：色と零・一の頂点を対にする。
規約：同じ色では頂点順は零から一への順。
使われ方：退化性の判定と次数制約。 -/
def edgePair {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (q : Fin (l + 1)) : Fin n × Fin 2 := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLabel u p q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeVertex p q)

/-- 概要：全ての色の出力が非退化である条件（BF §2.2.1）。
方針：同じ色で同じ頂点が二回現れないことを要求する。
規約：頂点列は単調なので、この条件が正規化後の非零性を表す。
使われ方：退化な切断項を零とする。 -/
def EdgeNondegenerate {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) : Prop :=
  Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair u p)

/-- 概要：辺の切断の非退化性は有限に判定できる（BF §2.2.1）。
方針：展開した全位置対を調べる。
規約：非計算的な選択を使わない。
使われ方：切断の有限和の係数を計算する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instDecidableEdgeNondegenerate {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) :
    Decidable (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate Function.Injective
  infer_instance

/-- 概要：切断点以前の位置は零頂点を与える（BF §2.2.1）。
方針：predAbove の前半の公式を使う。
規約：切断点そのものも含む。
使われ方：左側での退化性と具体的な係数計算。 -/
lemma edgePair_castSucc {n l : ℕ} (u : Fin l → Fin n) (p i : Fin l) (hi : i ≤ p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair u p i.castSucc = (u i, 0) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLabel, Fin.predAbove_castSucc_of_le _ _ hi]
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeVertex, Fin.le_def.mp hi]

/-- 概要：切断点以後の位置は一頂点を与える（BF §2.2.1）。
方針：predAbove の後半の公式を使う。
規約：切断点の複製した第二の位置も含む。
使われ方：右側での退化性と具体的な係数計算。 -/
lemma edgePair_succ {n l : ℕ} (u : Fin l → Fin n) (p i : Fin l) (hi : p ≤ i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair u p i.succ = (u i, 1) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLabel, Fin.predAbove_succ_of_le _ _ hi]
  have h : ¬ i.val + 1 ≤ p.val := by have := Fin.le_def.mp hi; omega
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeVertex, h]

/-- 概要：非退化な切断の同じ色の頂点列は狭義単調（BF §2.2.1）。
方針：全頂点列の単調性と、同じ色・頂点の単射性を組み合わせる。
規約：各色の連結順は元の展開位置の順。
使われ方：非零項の出力を実際の非退化な Δ¹ の単体と同定する。 -/
lemma edgeVertex_strictMono_on_fiber {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) {a b : Fin (l + 1)} (hab : a < b)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLabel u p a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLabel u p b) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeVertex p a < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeVertex p b := by
  apply lt_of_le_of_ne (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.monotone_edgeVertex p hab.le)
  intro he
  exact (ne_of_lt hab) (h (Prod.ext hc he))

/-- 概要：非退化な辺の切断では、辺を含む色は他には現れない（BF §2.2.1）。
方針：左右それぞれで同じ色・同じ頂点の一致を単射性で消去する。
規約：語の全射性や隣接非退化性は不要。
使われ方：切断点での微分と位置符号の整理。 -/
lemma pivot_unique {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (i : Fin l) (hi : u i = u p) : i = p := by
  rcases le_total i p with hip | hpi
  · have he : i.castSucc = p.castSucc := h (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_castSucc u p i hip,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_castSucc u p p le_rfl, hi])
    apply Fin.ext
    exact congrArg (fun q : Fin (l + 1) => q.val) he
  · have he : i.succ = p.succ := h (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_succ u p i hpi,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_succ u p p le_rfl, hi])
    apply Fin.ext
    have := congrArg Fin.val he
    simpa using this

/-- 概要：非退化な辺の切断には高々 2n 個の頂点しかない（BF §2.2.1）。
方針：展開した位置を色と二頂点の対へ単射で写し、濃度を比較する。
規約：arity 零も含む。
使われ方：必要な全射語の次数を有限範囲へ制限する。 -/
lemma edge_length_bound {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : l + 1 ≤ n * 2 := by
  simpa only [Fintype.card_fin, Fintype.card_prod] using
    Fintype.card_le_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair u p) h

/-- 概要：次数 d の語の非零な辺の切断は d+1≤n を満たす（BF §2.2）。
方針：長さ n+d と展開後の頂点数の上限を比較する。
規約：頂点への作用より一つ強い辺の制約。
使われ方：Δ¹ だけに特殊化した余演算の必要次数。 -/
lemma edge_degree_bound {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) : d + 1 ≤ n := by
  have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_length_bound h
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
