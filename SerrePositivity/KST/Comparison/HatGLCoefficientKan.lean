module

public import SerrePositivity.KST.Comparison.HatGLCoefficientHomotopy
public import SerrePositivity.KST.Comparison.SimplicialRingKan

/-!
# Kan 性の追加入力を持たない有限 rank の高次公式

概要：任意の単体的環の ĜL_r の正次数の群を零基点の係数群の行列と同定する。
方針：加法と退化による Kan 性を供給して有限 rank の比較を適用する。
規約：KST Lemma 2.13 の有限 rank の高次公式。安定 rank への自然性は別途証明する。
使われ方：ΓA に対する安定化後の高次の比較。
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
概要：任意の単体的環の有限 rank の ĜL の正次数の群の行列表示。
方針：実際のホーンの補正による Kan 性、可逆成分の包含、基点の平行移動、積分解を使う。
規約：添字 n は実際の次数 n+1。Kan 性や群完備化比較を仮定しない。
使われ方：KST Lemma 2.13 の rank の安定化前の具体的な群同型。
-/
def simplicialRingHatGLCoefficientHomotopyMulEquiv (A : SimplicialObject RingCat.{u})
    (r n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (hatGLSpace A r) n (1 : hatGLSubmonoid A r 0) ≃*
      (Fin r → Fin r → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))) :=
  hatGLCoefficientHomotopyMulEquiv A r n

end SerrePositivity.KST.Comparison
