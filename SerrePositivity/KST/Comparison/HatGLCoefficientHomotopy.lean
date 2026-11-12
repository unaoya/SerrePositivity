module

public import SerrePositivity.KST.Comparison.HatGLPositiveHomotopy
public import SerrePositivity.KST.Comparison.MatrixHomotopyProduct
public import SerrePositivity.KST.Comparison.RingBasepointTranslation

/-!
# 有限 rank の ĜL の正次数の群の係数表示

概要：ĜL_r の単位基点での正次数の群を、係数環の零基点での群の行列と同定する。
方針：可逆成分の包含、単位行列から零行列への平行移動、係数ごとの積分解を合成する。
規約：KST Lemma 2.13 の安定化前の高次公式。係数環の Kan 性を明示する。
使われ方：rank の安定化と高次の行列の余極限の公式。
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
概要：有限 rank の ĜL の正次数の群と係数環の零基点の群の行列の乗法同値。
方針：包含の比較、加法的平行移動、係数評価の積の同値を順に合成する。
規約：添字 n は次数 n+1。各単体次数の行列の乗法逆元は用いない。
使われ方：KST Lemma 2.13 の高次公式の有限 rank の部分。
-/
def hatGLCoefficientHomotopyMulEquiv (A : SimplicialObject RingCat.{u})
    [KanComplex (ringSpace A)] (r n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (hatGLSpace A r) n (1 : hatGLSubmonoid A r 0) ≃*
      (Fin r → Fin r → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))) :=
  (hatGLPositiveHomotopyMulEquiv A r (1 : hatGLSubmonoid A r 0) n).trans
    ((ringPositiveHomotopyBasepointEquiv (matrixRingObject A r)
      (1 : Matrix (Fin r) (Fin r) (A.obj (op ⦋0⦌))) n).trans
        (matrixPositiveHomotopyMulEquiv A r
          (0 : Matrix (Fin r) (Fin r) (A.obj (op ⦋0⦌))) n))

end SerrePositivity.KST.Comparison
