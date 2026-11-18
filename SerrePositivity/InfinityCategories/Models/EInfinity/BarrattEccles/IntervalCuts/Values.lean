module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.VertexCuts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Modules

/-!
模型。文献の定義との比較は後で
# Δ¹ の区間切断の符号付き基底値

概要：Berger–Fresse §2.2.6 の有限和を Δ¹ の零・一・辺の出力基底で定義する。
方針：各色の非空頂点集合を単体とし、非退化な切断だけを符号付きで足す。
規約：まだ複体射ではなく、実際の余演算を構成する基底上の値。
使われ方：区間のテンソル冪への作用の線形延長と微分・代入則の検証。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：Δ¹ の非退化な単体を非空の頂点集合で表す（BF §2.2.1）。
方針：二頂点の非空有限部分集合を取る。
規約：一元集合は頂点、二元集合は辺。
使われ方：区間の自由鎖加群とそのテンソル冪の基底。 -/
abbrev Simplex := {s : Finset (Fin 2) // s.Nonempty}

/-- 概要：指定した頂点の基底単体（BF §2.2.1）。
方針：一元の頂点集合を取る。
規約：零頂点と一頂点を同じ定義で扱う。
使われ方：端点の余代数射と切断の出力。 -/
def vertex (b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex := ⟨{b}, Finset.singleton_nonempty b⟩

/-- 概要：標準一単体の非退化な辺（BF §2.2.1）。
方針：二頂点の全体集合を取る。
規約：向きは零から一。
使われ方：区間の一次生成元と切断の出力。 -/
def edge : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex := ⟨Finset.univ, ⟨0, Finset.mem_univ _⟩⟩

/-- 概要：区間の非退化単体の鎖次数（BF §2.2.3）。
方針：頂点数から一を引く。
規約：頂点は零、辺は一。
使われ方：テンソル基底の総次数。 -/
def simplexDegree (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) : ℕ := s.val.card - 1

/-- 概要：非退化単体の次数は高々一（BF §2.2.1）。
方針：頂点集合が二頂点全体の部分集合であることを使う。
規約：空集合は基底に含めない。
使われ方：Δ¹ の次数零・一以外の成分を消去する。 -/
lemma simplexDegree_le_one (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s ≤ 1 := by
  have h := Finset.card_le_card (Finset.subset_univ s.val)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree
  omega

/-- 概要：全射語の辺の切断の出力基底族（BF §2.2.6）。
方針：各色の非空頂点集合を単体として並べる。
規約：非退化性は有限和へ入れるときに判定する。
使われ方：辺への作用の各項のテンソル基底。 -/
def edgeOutput {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d)) (k : Fin n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u.val p k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_nonempty u p k⟩

/-- 概要：非退化な切断の出力基底族の総次数は d+1（BF §2.2.3）。
方針：既存の全出力次数の計算を基底の次数で読み替える。
規約：入力は次数 d の語と辺。
使われ方：余演算を正しい次数のテンソル加群へ型付けする。 -/
lemma edgeOutput_total_degree {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    ∑ k : Fin n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k) = d + 1 :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_edgeOutputDegree u p h

variable (A : Type*) [CommRing A]

/-- 概要：辺の切断一項を出力基底上の有限台関数へ送る（BF §2.2.6）。
方針：非退化なら符号付き基底、退化なら零を返す。
規約：整数符号を係数環へ移す。
使われ方：辺の切断作用の有限和。 -/
def edgeTerm {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d)) :
    (Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) →₀ A :=
  if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p then Finsupp.single (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val p : A)
  else 0

/-- 概要：全射語の辺への区間切断作用の基底値（BF §2.2.6）。
方針：唯一の長い区間の位置について全て足す。
規約：全 arity・全語次数を定義し、退化項は自動的に零。
使われ方：χ の余演算の辺への評価。 -/
def edgeValue {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) : (Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) →₀ A :=
  ∑ p : Fin (n + d), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeTerm A u p

/-- 概要：全射語の頂点への区間切断作用の基底値（BF §2.2.6）。
方針：次数零なら全ての出力へ同じ頂点を置き、正次数なら零とする。
規約：空語の空テンソルへの値も一。
使われ方：χ の余演算の頂点への評価と端点射。 -/
def vertexValue {n d : ℕ} (_u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (b : Fin 2) : (Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) →₀ A :=
  if d = 0 then Finsupp.single (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) 1 else 0

/-- 概要：辺への切断作用を全射語の自由加群へ線形延長する（BF §2.2.6）。
方針：全射語基底の像として実際の符号付き有限和を指定する。
規約：入力語の次数 d と出力テンソル基底の総次数 d+1。
使われ方：余演算の複体射を構成する成分。 -/
def edgeLinear (n d : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d →ₗ[A] ((Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) →₀ A) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d).constr A (fun v => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeValue A v.down)

/-- 概要：頂点への切断作用を全射語の自由加群へ線形延長する（BF §2.2.6）。
方針：全射語基底の頂点への値を指定する。
規約：正次数は全て零。
使われ方：余演算の端点評価の成分。 -/
def vertexLinear (n d : ℕ) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d →ₗ[A] ((Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) →₀ A) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d).constr A (fun v => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexValue A v.down b)

/-- 概要：線形切断作用の辺での基底値は元の有限和（BF §2.2.6）。
方針：基底による線形延長を評価する。
規約：任意の可換環。
使われ方：複体射の微分・代入則を基底で検証する。 -/
@[simp] lemma edgeLinear_basis {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLinear A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up u)) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeValue A u := by
  exact Module.Basis.constr_basis (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d) A _ _

/-- 概要：次数上限を超えた辺の切断項は零（BF §2.2）。
方針：非退化な切断があれば d+1≤n に矛盾する。
規約：符号の相殺に依存せず各項が零。
使われ方：不要次数の余演算を定義段階で消去する。 -/
lemma edgeTerm_eq_zero_of_degree {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : n < d + 1) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeTerm A u p = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeTerm
  rw [ite_eq_right (fun hp => (not_le_of_gt h) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_degree_bound u p hp))]

/-- 概要：次数上限を超えた語の辺への作用は零（BF §2.2）。
方針：有限和の全項の零性を使う。
規約：零 arity も含む。
使われ方：区間の余演算の次数制限。 -/
lemma edgeValue_eq_zero_of_degree {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (h : n < d + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeValue A u = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeTerm_eq_zero_of_degree A u p h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
