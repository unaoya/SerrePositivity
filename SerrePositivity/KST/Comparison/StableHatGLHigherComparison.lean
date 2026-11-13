module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.HatGLRankCoefficientIso
public import SerrePositivity.KST.Comparison.BarPositiveDelooping
public import SerrePositivity.KST.Comparison.BarFundamentalMultiplication
public import Mathlib.CategoryTheory.Limits.Final

/-!
# KST Lemma 2.13 の安定分類空間の群の計算

概要：安定 ĜL の分類空間の基本群と全ての高次の群を具体的に同定する。
方針：有限 rank の自然同型の余極限、rank の圏同値、標準群完備化の delooping を合成する。
規約：KST Lemma 2.13。π_n とその群演算・余極限の定理は K-L9 から借り、追加仮定は置かない。
使われ方：plus 構成と KST Proposition 2.15 の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite SSet
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：Kan 置換したモノイドの bar も連結である。
方針：置換の単位の成分の全単射で元の bar の連結性を移す。
規約：群状性はこの連結性には不要。
使われ方：KST Lemma 2.13 の連結な分類空間。
-/
instance monoidBarKanConnected (M : SimplicialObject MonCat.{u}) :
    (monoidBarKanPointed M).right.IsConnected where
  nonempty := ⟨(monoidBarKanPointed M).basepoint⟩
  allEq a b := by
    let q : monoidBar M ⟶ (monoidBarKanPointed M).right :=
      AnodyneKanReplacement.unit.app (monoidBar M)
    have hq : IsIso (AnodyneHomotopy.anodyneQ.map q) :=
      Localization.inverts _ anodyneExtensions q (AnodyneKanReplacement.unit_anodyne _)
    have hb := PiZeroLocalization.piZero_bijective q hq
    obtain ⟨x, rfl⟩ := hb.surjective a
    obtain ⟨y, rfl⟩ := hb.surjective b
    exact congrArg (mapπ₀ q) (Subsingleton.elim x y)

/--
概要：安定 ĜL の正次数の群を安定係数行列群と同定する群の圏の同型。
方針：群の余極限の比較と有限 rank の自然同型の余極限を合成し、rank の同値を取り除く。
規約：KST Lemma 2.13 の安定 ĜL 自身の高次公式。
使われ方：分類空間の一つ上の次数の群の計算。
-/
def stableHatGLCoefficientHomotopyIso (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    GrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidSpace (stableHatGL A)) n
        (monoidPointed (stableHatGL A)).basepoint) ≅
      stableCoefficientMatrices
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))) :=
  (stableHatGLHomotopyGroupColimitIso A n).symm ≪≫
    HasColimit.isoOfNatIso (hatGLRankCoefficientIso A n) ≪≫
      Functor.Final.colimitIso liftedRankEquivalence.functor
        (coefficientMatrixRankSequence
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))))

/--
概要：安定 ĜL の正次数の群と安定係数行列群の乗法同値。
方針：群の圏の実際の同型から乗法同値を取り出す。
規約：係数は零基点の群、添字 n は実際の次数 n+1。
使われ方：KST Lemma 2.13 の高次の群の同定。
-/
def stableHatGLCoefficientHomotopyMulEquiv (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidSpace (stableHatGL A)) n
        (monoidPointed (stableHatGL A)).basepoint ≃*
      stableCoefficientMatrices
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))) :=
  (stableHatGLCoefficientHomotopyIso A n).groupIsoToMulEquiv

/--
概要：BĜL の基本群は安定 GL(π₀A) と群として同型である。
方針：可逆成分の計算と標準群完備化の辺の乗法の比較を適用する。
規約：KST Lemma 2.13 の i=1。SingleObj の合成の向きに合わせて逆元の辺を用いる。
使われ方：plus による基本群の商と K₁ の比較。
-/
def lemma_2_13_pi_one (A : SimplicialObject RingCat.{u}) :
    stableGeneralLinear (π₀ (ringSpace A)) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidBarKanPointed (stableHatGL A)).right 0
        (monoidBarKanPointed (stableHatGL A)).basepoint :=
  stableHatGLBarFundamentalMulEquiv A

/--
概要：BĜL の次数 n+2 の群は係数環の次数 n+1 の群の安定行列群と同型である。
方針：標準群完備化の delooping と、自然な有限 rank の係数表示の余極限を合成する。
規約：KST Lemma 2.13 の i>1。Kan 性、比較の同値性、rank の余極限に追加仮定は無い。
使われ方：KST §2 の比較定理と plus 構成への入力。
-/
def lemma_2_13_higher (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidBarKanPointed (stableHatGL A)).right (n + 1)
        (monoidBarKanPointed (stableHatGL A)).basepoint ≃*
      stableCoefficientMatrices
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))) :=
  (stableHatGLBarPositiveHomotopyMulEquiv A n).symm.trans
    (stableHatGLCoefficientHomotopyMulEquiv A n)

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Lemma 2.13" (partial := special) "仮定：単位つき単体環（Lean が強い：原典は非単位的環も含む）。結論：安定 GL(π₀) の基本群同型と高次の安定係数行列群の同型（原典の単位つきの場合と一致）。"] _root_.SerrePositivity.KST.Comparison.lemma_2_13_higher
attribute [cite KST "Lemma 2.13" (partial := special) "仮定：単位つき単体環（Lean が強い：原典は非単位的環も含む）。結論：安定 GL(π₀) の基本群同型と高次の安定係数行列群の同型（原典の単位つきの場合と一致）。"] _root_.SerrePositivity.KST.Comparison.lemma_2_13_pi_one
