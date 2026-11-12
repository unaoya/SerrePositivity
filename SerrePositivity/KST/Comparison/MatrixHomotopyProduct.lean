module

public import SerrePositivity.KST.Comparison.MatrixPointedSimplex

/-!
# 全行列の正次数のホモトピー群の積分解

概要：全行列の正次数のホモトピー群を係数ごとの対応する群の積と同定する。
方針：係数評価の誘導準同型の全単射性を、代表と同じ添字の関係の組み立てで示す。
規約：KST Lemma 2.13 の有限 rank の高次公式。基点の各係数を明示する。
使われ方：単位行列から零行列への基点移動と安定化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：正次数のホモトピー群を全係数の群へ送る準同型。
方針：各係数評価の誘導準同型を束ねる。
規約：全行列の基点 a の各係数 a_ij を係数群の基点とする。
使われ方：行列のホモトピー群の具体的な積分解。
-/
def matrixHomotopyEntryHom (A : SimplicialObject RingCat.{u}) (r : ℕ)
    [KanComplex (ringSpace A)] (a : (matrixSpace A r) _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (matrixSpace A r) n a →*
      (∀ i j : Fin r, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (a i j)) where
  toFun x i j := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (matrixEntryMap A r i j) rfl x
  map_one' := by
    funext i j
    exact map_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (matrixEntryMap A r i j) rfl)
  map_mul' x y := by
    funext i j
    exact map_mul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (matrixEntryMap A r i j) rfl) x y

/--
概要：行列のホモトピー群の係数写像は全単射。
方針：係数ごとの代表を束ね、類の一致から同じ零番目の関係を選んで束ねる。
規約：係数の Kan 性は共通の面添字の RelStruct への変換で用いる。
使われ方：具体的な積分解の群同型。
-/
theorem matrixHomotopyEntryHom_bijective (A : SimplicialObject RingCat.{u}) (r : ℕ)
    [KanComplex (ringSpace A)] (a : (matrixSpace A r) _⦋0⦌) (n : ℕ) :
    Function.Bijective (matrixHomotopyEntryHom A r a n) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with | h f => ?_
    induction y using Quotient.inductionOn with | h g => ?_
    have he (i j : Fin r) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (matrixEntryMap A r i j) rfl f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (matrixEntryMap A r i j) rfl g) :=
      congrFun (congrFun hxy i) j
    have hr (i j : Fin r) := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (0 : Fin (n + 2))).1
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff _ _).1 (he i j))
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound
      (matrixRelStruct A r (n + 1) a (fun i j => Classical.choice (hr i j)))
  · intro b
    have hs (i j : Fin r) : ∃ s : (ringSpace A).PtSimplex (n + 1) (a i j),
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = b i j := Quotient.mk_surjective _
    choose f hf using hs
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (matrixPtSimplex A r (n + 1) a f), ?_⟩
    funext i j
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (matrixEntryMap A r i j) rfl
      (matrixPtSimplex A r (n + 1) a f)) = b i j
    rw [matrixPtSimplex_entry]
    exact hf i j

/--
概要：全行列の正次数の群と係数ごとの正次数の群の積の乗法同値。
方針：係数評価の準同型とその全単射性を合わせる。
規約：KST Lemma 2.13 の有限 rank の積の比較。π_n を新たに定義しない。
使われ方：ĜL の正次数の群から係数のホモトピー群の行列への接続。
-/
def matrixPositiveHomotopyMulEquiv (A : SimplicialObject RingCat.{u}) (r : ℕ)
    [KanComplex (ringSpace A)] (a : (matrixSpace A r) _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (matrixSpace A r) n a ≃*
      (∀ i j : Fin r, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (a i j)) :=
  MulEquiv.ofBijective (matrixHomotopyEntryHom A r a n)
    (matrixHomotopyEntryHom_bijective A r a n)

end SerrePositivity.KST.Comparison
