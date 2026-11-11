module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.ThinNerveInnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
概要：前順序の nerve へのホーンの射の頂点とその単体への延長。
方針：各頂点の像を取り、単調な頂点列を nerve の単体として Yoneda で戻す。
規約：ホーンの次元は二以上。
使われ方：Kerodon §5.1.1（Tag 01T4）、Theorem 5.3.5.7（Tag 037Q）、有限鎖の最初の辺の cocartesian 性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：前順序の nerve へのホーンの射が選ぶ各頂点の像。
方針：標準頂点をホーンへ持ち上げ、像の零単体の対象を取る。
規約：欠けた面の番号を i、選ぶ頂点を j とする。
使われ方：Kerodon §5.1.1（Tag 01T4）、ホーンの延長の頂点データ。 -/
def preorderNerveHornVertex {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C) (j : Fin (n + 3)) : C :=
  (a.app (Opposite.op ⦋0⦌)
    ⟨stdSimplex.obj₀Equiv.symm j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn n i _⟩).obj 0

/-- 概要：ホーンの射はその単体としての頂点を評価しても同じ頂点データを与える。
方針：零単体は唯一の頂点の値で決まることを使う。
規約：v はホーンの任意の零単体。
使われ方：Kerodon §5.1.1（Tag 01T4）、標準頂点とホーンの頂点の表示を揃える。 -/
lemma preorderNerveHornVertex_apply {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C)
    (v : (horn (n + 2) i : SSet.{u}) _⦋0⦌) :
    preorderNerveHornVertex a (v.val 0) = (a.app _ v).obj 0 := by
  have hv : (⟨stdSimplex.obj₀Equiv.symm (v.val 0), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn n i _⟩ :
      (horn (n + 2) i : SSet.{u}) _⦋0⦌) = v := by
    apply Subtype.ext
    apply stdSimplex.ext
    intro j
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst j
    rfl
  unfold preorderNerveHornVertex
  rw [hv]

/-- 概要：頂点列が単調である前順序の nerve へのホーンの射は単体全体へ延長できる。
方針：単調な頂点列の関手を Yoneda で単体の射とし、頂点で制限を比較する。
規約：内側・外側のホーンを共に扱う。
使われ方：Kerodon §5.1.1（Tag 01T4）、有限鎖の外側ホーンの持ち上げ。 -/
lemma preorderNerveHorn_extend {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C)
    (ha : Monotone (preorderNerveHornVertex a)) :
    ∃ l : (Δ[n + 2] : SSet.{u}) ⟶ nerve C, (horn (n + 2) i).ι ≫ l = a := by
  let σ : ComposableArrows C (n + 2) := ha.functor
  refine ⟨SSet.yonedaEquiv.symm σ, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro v
  apply ComposableArrows.ext₀
  change preorderNerveHornVertex a (v.val 0) = (a.app _ v).obj 0
  exact preorderNerveHornVertex_apply a v

/-- 概要：ホーンに含まれる辺の像の両端は対応する頂点データ。
方針：辺の像の始点・終点を自然性で同定し、その対象を比較する。
規約：辺の存在条件は三頂点の有限集合の濃度で指定する。
使われ方：Kerodon §5.1.1（Tag 01T4）、外側ホーンの頂点列の単調性。 -/
lemma preorderNerveHornVertex_edge_objs {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C)
    (j k : Fin (n + 3)) (hjk : j ≤ k) (hc : Finset.card {i, j, k} ≤ n + 2) :
    (a.app (Opposite.op ⦋1⦌) (horn.edge (n + 2) i j k hjk hc)).obj 0 =
        preorderNerveHornVertex a j ∧
      (a.app (Opposite.op ⦋1⦌) (horn.edge (n + 2) i j k hjk hc)).obj 1 =
        preorderNerveHornVertex a k := by
  let e := horn.edge (n + 2) i j k hjk hc
  let τ := a.app (Opposite.op ⦋1⦌) e
  have h0 := congrArg (fun s : (nerve C) _⦋0⦌ ↦ s.obj 0)
    (ConcreteCategory.congr_hom (a.naturality (SimplexCategory.δ (1 : Fin 2)).op) e)
  have h1 := congrArg (fun s : (nerve C) _⦋0⦌ ↦ s.obj 0)
    (ConcreteCategory.congr_hom (a.naturality (SimplexCategory.δ (0 : Fin 2)).op) e)
  let v0 := (horn (n + 2) i : SSet.{u}).map (SimplexCategory.δ (1 : Fin 2)).op e
  let v1 := (horn (n + 2) i : SSet.{u}).map (SimplexCategory.δ (0 : Fin 2)).op e
  change (a.app _ v0).obj 0 = τ.obj 0 at h0
  change (a.app _ v1).obj 0 = τ.obj 1 at h1
  rw [← preorderNerveHornVertex_apply a v0] at h0
  rw [← preorderNerveHornVertex_apply a v1] at h1
  have hv0 : v0.val 0 = j := rfl
  have hv1 : v1.val 0 = k := rfl
  rw [hv0] at h0
  rw [hv1] at h1
  exact ⟨h0.symm, h1.symm⟩

/-- 概要：ホーンに含まれる辺は頂点データの順序関係を与える。
方針：辺の像の両端の計算に射の存在から得られる順序関係を適用する。
規約：辺の存在条件は三頂点の有限集合の濃度で指定する。
使われ方：Kerodon §5.1.1（Tag 01T4）、外側ホーンの頂点列の単調性。 -/
lemma preorderNerveHornVertex_le {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C)
    (j k : Fin (n + 3)) (hjk : j ≤ k) (hc : Finset.card {i, j, k} ≤ n + 2) :
    preorderNerveHornVertex a j ≤ preorderNerveHornVertex a k := by
  have he := preorderNerveHornVertex_edge_objs a j k hjk hc
  rw [← he.1, ← he.2]
  exact leOfHom ((a.app (Opposite.op ⦋1⦌) (horn.edge (n + 2) i j k hjk hc)).map
    (homOfLE (show (0 : Fin 2) ≤ 1 from by decide)))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
