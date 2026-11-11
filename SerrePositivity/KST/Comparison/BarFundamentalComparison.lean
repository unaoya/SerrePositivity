module

public import SerrePositivity.KST.Comparison.GroupCompletionHomotopy
public import SerrePositivity.KST.Comparison.StableGLComponents

/-!
# 分類空間の基本群の台集合と成分の比較

概要：群状モノイドの実際の成分と分類空間の基本群の台集合を同定する。
方針：成分の Kan 置換不変性、K-L9 の零次数との比較、群完備化の次数移動を合成する。
規約：KST Lemma 2.13 の零次数から一次への比較。ここでは群演算との整合を主張しない。
使われ方：安定一般線形群との具体的な全単射。群同型への強化は別途検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：群状モノイドの成分と分類空間の基本群の台集合の同値。
方針：anodyne な置換単位で成分を移し、零次数のホモトピー類と loop の次数移動を使う。
規約：入力の Kan 性は不要。群演算との整合はこの宣言の結論に含めない。
使われ方：KST Lemma 2.13 の i=1 の台集合の比較。
-/
def monoidBarFundamentalEquiv (M : SimplicialObject MonCat.{u})
    (hM : SimplicialMonoid.IsGrouplike M) :
    π₀ (monoidSpace M) ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidBarKanPointed M).right 0
      (monoidBarKanPointed M).basepoint := by
  let R := Spectra.PointedKanReplacement.obj (monoidPointed M)
  let i := AnodyneKanReplacement.unit.app (monoidSpace M)
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map i) :=
    Localization.inverts _ anodyneExtensions i (AnodyneKanReplacement.unit_anodyne _)
  exact (Equiv.ofBijective (mapπ₀ i) (PiZeroLocalization.piZero_bijective i hi)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := R.right) (x := R.basepoint)).symm.trans
      (monoidBarHomotopyEquiv M hM 0))

/--
概要：安定 GL(π₀A) と BĜL(A) の基本群の台集合の同値。
方針：実際の安定成分モノイドの同型と分類空間の基本群の比較を合成する。
規約：KST Lemma 2.13 の i=1。π_n の模型は K-L9 の Kan 置換を使う。
使われ方：基本群の群演算との整合を検証する具体的な比較。
-/
def stableHatGLBarFundamentalEquiv (A : SimplicialObject RingCat.{u}) :
    stableGeneralLinear (π₀ (ringSpace A)) ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidBarKanPointed (stableHatGL A)).right 0
        (monoidBarKanPointed (stableHatGL A)).basepoint :=
  (Iso.monCatIsoToMulEquiv (stableHatGLComponentsIso A)).symm.toEquiv.trans
    (monoidBarFundamentalEquiv (stableHatGL A) (stableHatGL_isGrouplike A))

end SerrePositivity.KST.Comparison
