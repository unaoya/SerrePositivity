module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedInterval
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.NormalizationDescent

/-!
模型。文献の定義との比較は後で
# 実際の正規化区間の二頂点・一辺で指定する線形写像

概要：Berger–Fresse §2.2.6 の区間切断値を実際の正規化区間の入力へ線形化する。
方針：自由単体加群の値を Moore 複体へ降下し、零次の二頂点と一次の一辺で評価する。
規約：任意の係数加群への写像を構成し、外部の基底や複体射は仮定しない。
使われ方：χ(n) と区間の全整数次数の双線形成分の構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：零次単体の値から実際の正規化零次区間への線形写像を作る（BF §2.2.6）。
方針：唯一の頂点を読み、自由加群の写像を Moore 部分加群へ制限する。
規約：零次には退化の降下条件はない。
使われ方：二頂点の切断値を実際の区間入力へ延長する。 -/
def vertexChainLift (M : ModuleCat.{u} A) (v : Fin 2 → M) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).X 0 ⟶ M :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.restrictToNormalized ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Δ[1]) 0
    (ModuleCat.freeDesc (↾fun x : ULift.{u} (Δ[1] _⦋0⦌) =>
      v ((SSet.stdSimplex.objEquiv x.down).toOrderHom 0)))

/-- 概要：正規化零次単体への線形写像はその頂点の指定値を返す（BF §2.2.6）。
方針：退化条件が空である正規化降下の評価を使う。
規約：全ての零次単体を扱う。
使われ方：頂点値と線形延長の照合。 -/
lemma vertexChainLift_generator (M : ModuleCat.{u} A) (v : Fin 2 → M)
    (x : Δ[1] _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChainLift A M v (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] 0 x) =
      v ((SSet.stdSimplex.objEquiv x).toOrderHom 0) := by
  have h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization_restrictToNormalized
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Δ[1]) 0
    (ModuleCat.freeDesc (M := M) (↾fun x : ULift.{u} (Δ[1] _⦋0⦌) =>
      v ((SSet.stdSimplex.objEquiv x.down).toOrderHom 0))) (fun k e _ => by omega)
  have hv := congrArg (fun f => f (ModuleCat.freeMk (ULift.up x))) h
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChainLift A M v (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] 0 x) =
    ModuleCat.freeDesc (M := M) (↾fun x : ULift.{u} (Δ[1] _⦋0⦌) =>
      v ((SSet.stdSimplex.objEquiv x.down).toOrderHom 0))
        (ModuleCat.freeMk (ULift.up x)) at hv
  erw [ModuleCat.freeDesc_apply] at hv
  exact hv

/-- 概要：実際の端点生成元は指定した二頂点値へ移る（BF §2.2.6）。
方針：標準定数零単体に生成元公式を適用する。
規約：零・一の両頂点。
使われ方：余演算の頂点入力の評価。 -/
@[simp] lemma vertexChainLift_vertex (M : ModuleCat.{u} A) (v : Fin 2 → M) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChainLift A M v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b) = v b :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChainLift_generator A M v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexSimplex b)

/-- 概要：退化した一単体は標準辺と異なる（BF §2.2.1）。
方針：退化辺の二端点は等しいが標準辺の二端点は異なる。
規約：任意の入力頂点に成立する。
使われ方：指定辺値の正規化への降下。 -/
lemma degenerateEdge_ne_edge (x : Δ[1] _⦋0⦌) :
    (Δ[1] : SSet).σ 0 x ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex := by
  intro h
  have he := congrArg SSet.stdSimplex.objEquiv h
  have h0 := congrArg (fun θ : ⦋1⦌ ⟶ ⦋1⦌ => θ.toOrderHom 0) he
  have h1 := congrArg (fun θ : ⦋1⦌ ⟶ ⦋1⦌ => θ.toOrderHom 1) he
  change (SSet.stdSimplex.objEquiv x).toOrderHom 0 = 0 at h0
  change (SSet.stdSimplex.objEquiv x).toOrderHom 0 = 1 at h1
  exact (by decide : (0 : Fin 2) ≠ 1) (h0.symm.trans h1)

/-- 概要：標準辺の値を指定する自由一単体加群上の写像（BF §2.2.6）。
方針：標準辺だけを指定値へ送り、他の二つの退化辺を零へ送る。
規約：後で退化消滅を証明して正規化へ降下する。
使われ方：実際の区間の辺入力の線形延長。 -/
def rawEdgeLift (M : ModuleCat.{u} A) (e : M) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Δ[1]) _⦋1⦌ ⟶ M :=
  ModuleCat.freeDesc (↾fun x : ULift.{u} (Δ[1] _⦋1⦌) => if x.down = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex then e else 0)

/-- 概要：指定辺値の自由線形写像は全ての退化成分を消す（BF §2.2.6）。
方針：唯一の退化位置で自由生成元を評価し、退化辺と標準辺の不一致を使う。
規約：次数移送の証明を含む正規化降下の条件。
使われ方：辺の線形写像を実際の Moore 成分へ降下する。 -/
lemma rawEdgeLift_degeneracies_zero (M : ModuleCat.{u} A) (e : M)
    (k : ℕ) (hk : k + 1 = 1) (i : Fin (k + 1)) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Δ[1]).σ i ≫
      eqToHom (congrArg (fun j => ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Δ[1]) _⦋j⦌) hk) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.rawEdgeLift A M e = 0 := by
  have hk0 : k = 0 := by omega
  subst k
  fin_cases i
  simp only [eqToHom_refl]
  apply ModuleCat.free_hom_ext
  intro ⟨x⟩
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.rawEdgeLift A M e
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Δ[1]).σ 0 (ModuleCat.freeMk (ULift.up x))) = 0
  erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply]
  exact ite_eq_right (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.degenerateEdge_ne_edge x)

/-- 概要：辺の指定値を実際の正規化一次区間へ線形延長する（BF §2.2.6）。
方針：退化辺を消す自由写像を Moore 部分加群へ制限する。
規約：任意の係数加群と任意の指定辺値。
使われ方：余演算の辺入力の双線形成分。 -/
def edgeChainLift (M : ModuleCat.{u} A) (e : M) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).X 1 ⟶ M :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.restrictToNormalized ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Δ[1]) 1
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.rawEdgeLift A M e)

/-- 概要：正規化一単体は標準辺なら指定値、退化辺なら零へ移る（BF §2.2.6）。
方針：退化消滅による正規化降下の等式を生成元で評価する。
規約：全ての一単体を扱う。
使われ方：実際の辺入力に対する線形写像の評価。 -/
lemma edgeChainLift_generator (M : ModuleCat.{u} A) (e : M) (x : Δ[1] _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChainLift A M e (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] 1 x) =
      if x = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex then e else 0 := by
  have h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization_restrictToNormalized
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Δ[1]) 1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.rawEdgeLift A M e)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.rawEdgeLift_degeneracies_zero A M e)
  have hv := congrArg (fun f => f (ModuleCat.freeMk (ULift.up x))) h
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChainLift A M e (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] 1 x) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.rawEdgeLift A M e (ModuleCat.freeMk (ULift.up x)) at hv
  erw [ModuleCat.freeDesc_apply] at hv
  exact hv

/-- 概要：実際の標準辺生成元は指定辺値へ移る（BF §2.2.6）。
方針：標準辺を生成元公式へ代入する。
規約：向きは零から一。
使われ方：余演算の辺入力の評価。 -/
@[simp] lemma edgeChainLift_edge (M : ModuleCat.{u} A) (e : M) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChainLift A M e (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A) = e := by
  simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChainLift_generator A M e _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
