module

public import SerrePositivity.EInfinity.BarrattEccles.ShufflePaths
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Preorder.Finite

/-!
模型。文献の定義との比較は後で
# 任意次元の単体の区間切断の展開

Berger–Fresse §2.2.1・§2.2.6 の切断を格子経路で表す。
m+1 個の区間と q 個の単体の辺を走る経路の各頂点に、区間の色と単体の頂点を付ける。
これは top operation の非零項の支持の計算であり、作用全体や符号の計算ではない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- m+1 個の切断区間を持つ q 単体の切断。水平ステップは次の区間へ移る。 -/
abbrev Cut (m q : ℕ) := ShufflePath m q

def label {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (u : Fin (m + 1) → Fin r)
    (i : Fin (m + q + 1)) : Fin r := u (s.horizontal i)

def pair {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (u : Fin (m + 1) → Fin r)
    (i : Fin (m + q + 1)) : Fin r × Fin (q + 1) := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u i, s.vertical i)

/-- 各色に集めた頂点列に重複がない、正規化した切断項の非退化性。 -/
def Nondegenerate {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (u : Fin (m + 1) → Fin r) : Prop :=
  Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.pair s u)

instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.instDecidableNondegenerate {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (u : Fin (m + 1) → Fin r) :
    Decidable (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s u) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate Function.Injective
  infer_instance

lemma vertex_strictMono_on_color {m q r : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q} {u : Fin (m + 1) → Fin r}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s u) {i j : Fin (m + q + 1)} (hij : i < j)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u j) : s.vertical i < s.vertical j := by
  apply lt_of_le_of_ne (s.vertical.monotone hij.le)
  intro hv
  exact (ne_of_lt hij) (h (Prod.ext hc hv))

lemma length_bound {m q r : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q} {u : Fin (m + 1) → Fin r}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s u) : m + q + 1 ≤ r * (q + 1) := by
  simpa only [Fintype.card_fin, Fintype.card_prod] using
    Fintype.card_le_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.pair s u) h

/-- 一つの色に集める展開位置を、元の順序で保持する。 -/
def colorPositions {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (u : Fin (m + 1) → Fin r) (a : Fin r) :
    Finset (Fin (m + q + 1)) := Finset.univ.filter (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u i = a)

/-- 出力次数 q の色の頂点列を、実際の順序で列挙する。 -/
def fullColorVertices {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (u : Fin (m + 1) → Fin r) (a : Fin r)
    (hcard : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).card = q + 1) : Fin (q + 1) → Fin (q + 1) :=
  fun i => s.vertical ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).orderEmbOfFin hcard i)

lemma fullColorVertices_strictMono {m q r : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q} {u : Fin (m + 1) → Fin r}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s u) (a : Fin r) (hcard : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).card = q + 1) :
    StrictMono (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorVertices s u a hcard) := by
  intro i j hij
  have hi := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).orderEmbOfFin_mem hcard i
  have hj := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).orderEmbOfFin_mem hcard j
  have hi' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).orderEmbOfFin hcard i) = a :=
    (Finset.mem_filter.mp hi).2
  have hj' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).orderEmbOfFin hcard j) = a :=
    (Finset.mem_filter.mp hj).2
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertex_strictMono_on_color h
    (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).orderEmbOfFin hcard).strictMono hij) (hi'.trans hj'.symm)

/-- 非退化な q 単体で q+1 個の頂点を持つ色は、全単体を恒等順序で読む。 -/
lemma fullColorVertices_eq_id {m q r : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q} {u : Fin (m + 1) → Fin r}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s u) (a : Fin r) (hcard : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).card = q + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorVertices s u a hcard = id :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorVertices_strictMono h a hcard).eq_id

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
