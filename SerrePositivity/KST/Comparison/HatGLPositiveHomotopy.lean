module

public import SerrePositivity.KST.Comparison.HatGLComponentIso
public import SerrePositivity.KST.Comparison.ComponentHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
# ĜL の正次数の群は全行列の群で計算できる

概要：全行列の台集合が Kan であるとき、ĜL の包含は正次数のホモトピー群を保つ。
方針：可逆成分全体との実際の同型を通し、成分部分複体の包含の群同型を適用する。
規約：KST 式 (2.2)、Lemma 2.13 の有限 rank の可逆成分の比較。
使われ方：係数のホモトピー群の行列による高次公式への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

/--
概要：ĜL の全行列への実際の包含。
方針：各次数で部分型の値を取る。
規約：単体的群への包含とは主張しない。
使われ方：正次数のホモトピー群の比較の基礎射。
-/
def hatGLMatrixInclusion (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    hatGLSpace A r ⟶ matrixSpace A r where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

/--
概要：全行列の台集合が Kan なら ĜL の台集合も Kan である。
方針：成分部分複体の Kan 性を実際の同型で移す。
規約：全行列の Kan 性を明示する。
使われ方：K-L9 の正次数の群の定義への入力。
-/
instance hatGLSpace_kanComplex (A : SimplicialObject RingCat.{u}) (r : ℕ)
    [KanComplex (matrixSpace A r)] : KanComplex (hatGLSpace A r) :=
  isFibrant_of_fibration (hatGLComponentIso A r).hom

/--
概要：ĜL と全行列の選ばれた基点での正次数のホモトピー群の同型。
方針：成分全体との同型と成分部分複体の包含の群同型を合成する。
規約：添字 n は実際の次数 n+1。元の環への Kan 性の仮定は全行列のものから区別する。
使われ方：KST Lemma 2.13 の高次の行列公式の有限 rank の段階。
-/
def hatGLPositiveHomotopyMulEquiv (A : SimplicialObject RingCat.{u}) (r : ℕ)
    [KanComplex (matrixSpace A r)] (a : (hatGLSpace A r) _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (hatGLSpace A r) n a ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (matrixSpace A r) n a.val :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (hatGLComponentIso A r) rfl).trans
    (componentPositiveHomotopyMulEquiv (matrixSpace A r)
      (fun c => IsUnit (matrixComponentMap A r c)) ((hatGLComponentIso A r).hom.app _ a) n)

/--
概要：正次数の比較は実際の全行列への包含が誘導する写像である。
方針：群同型を構成した二つの射の合成を K-L9 の誘導写像の合成則で計算する。
規約：単なる抽象的な群同型でなく包含との整合を示す。
使われ方：rank の安定化との自然性。
-/
theorem hatGLPositiveHomotopyMulEquiv_apply (A : SimplicialObject RingCat.{u}) (r : ℕ)
    [KanComplex (matrixSpace A r)] (a : (hatGLSpace A r) _⦋0⦌) (n : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (hatGLSpace A r) n a) :
    hatGLPositiveHomotopyMulEquiv A r a n x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (hatGLMatrixInclusion A r) rfl x := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map _ rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (hatGLComponentIso A r).hom rfl x) = _
  exact (DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n)
    (hatGLComponentIso A r).hom rfl
    (componentSubcomplex (matrixSpace A r) (fun c => IsUnit (matrixComponentMap A r c))).ι
    rfl rfl) x).symm

end SerrePositivity.KST.Comparison
