module

public import SerrePositivity.KST.Comparison.MatrixSpace
public import SerrePositivity.KST.Comparison.GLComponents
public import SerrePositivity.KST.Comparison.ComponentSubcomplex

/-!
# ĜL は全行列の可逆成分全体である

概要：ĜL の台単体集合を全行列の成分を選んだ部分複体と同定する。
方針：全行列の成分から係数ごとの成分行列を作り、各次数の条件を比較する。
規約：KST 式 (2.2)、Lemma 2.13 の可逆成分の意味。
使われ方：正次数のホモトピー群を全行列のホモトピー群と同定する。
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
概要：全行列の辺から一つの係数の辺を取り出す。
方針：行・列で評価し、端点の等式も係数で評価する。
規約：可逆性の条件は課さない。
使われ方：成分から成分行列への写像の代表独立性。
-/
def matrixCoefficientEdge (A : SimplicialObject RingCat.{u}) (r : ℕ)
    {a b : (matrixSpace A r) _⦋0⦌} (e : (matrixSpace A r).Edge a b) (i j : Fin r) :
    (ringSpace A).Edge (a i j) (b i j) :=
  .mk (e.edge i j) (congrArg (fun t => t i j) e.src_eq)
    (congrArg (fun t => t i j) e.tgt_eq)

/--
概要：全行列の連結成分を係数ごとの成分行列へ送る。
方針：零次の成分行列の写像を辺の関係に関して商へ降ろす。
規約：乗法の整合性をこの宣言には含めない。
使われ方：可逆な成分の性質を π₀ 上で指定する。
-/
def matrixComponentMap (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    π₀ (matrixSpace A r) → Matrix (Fin r) (Fin r) (π₀ (ringSpace A)) :=
  π₀.lift (matrixToComponents A r 0) (by
    intro a b e
    apply Matrix.ext
    intro i j
    rw [matrixToComponents_zero_entry, matrixToComponents_zero_entry]
    exact π₀.sound (matrixCoefficientEdge A r e i j))

/--
概要：任意の単体の成分行列はその成分の像である。
方針：最初の頂点への引き戻しと成分行列の自然性を使う。
規約：各次数の単元性と成分全体の単元性を一致させる。
使われ方：ĜL と可逆成分の部分複体の同型。
-/
theorem matrixComponentMap_simplex (A : SimplicialObject RingCat.{u}) (r n : ℕ)
    (a : (matrixSpace A r) _⦋n⦌) :
    matrixComponentMap A r (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass (matrixSpace A r) a) = matrixToComponents A r n a :=
  matrixToComponents_natural A r (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) a

/--
概要：ĜL の台単体集合と全行列の可逆成分全体の部分複体の同型。
方針：行列自体を変えず、成分行列の式で二つの部分型の条件を同定する。
規約：各単体次数での strict な可逆性を要求しない。KST 式 (2.2)。
使われ方：可逆成分の包含の正次数の群同型の適用。
-/
def hatGLComponentIso (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    hatGLSpace A r ≅ (componentSubcomplex (matrixSpace A r)
      (fun c => IsUnit (matrixComponentMap A r c)) : SSet) :=
  NatIso.ofComponents (fun n => (show (hatGLSpace A r).obj n ≃
      (componentSubcomplex (matrixSpace A r)
        (fun c => IsUnit (matrixComponentMap A r c)) : SSet).obj n from
    { toFun := fun a => ⟨a.val, by
        change IsUnit (matrixComponentMap A r (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass (matrixSpace A r) a.val))
        rw [matrixComponentMap_simplex]
        exact a.property⟩
      invFun := fun a => ⟨a.val, by
        change IsUnit (matrixToComponents A r n.unop.len a.val)
        rw [← matrixComponentMap_simplex]
        exact a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).toIso) (by
    intro m n f
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    rfl)

end SerrePositivity.KST.Comparison
