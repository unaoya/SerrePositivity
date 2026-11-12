module
public import SerrePositivity.KST.ProExcision.SimplicialIdealGroups
public import SerrePositivity.KST.ProExcision.DiagonalGroupHomotopy

/-!
# 単体的イデアル上の実 m 次帰納ホモトピー

概要：非可換な単体的イデアル上の右乗法 φ の対角 C(H) 上の実 m 次比較を構成する。
方針：次数ごとの関手的な実帰納比較を既存の対角 bar へ制限する。
規約：KST Lemma 4.16 の非可換版。非被約 C(H)、A.5 の augmentation 補正を維持する。
使われ方：行列同変性を添えて A.4 の相対零化へ渡す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：単体的イデアル上の右乗法を対角 C(H) 内で m 次まで自明射と比較する実ホモトピー。
方針：離散環上の構成と全ての係数射に対する自然性を対角の実区間に移す。
規約：KST Lemma 4.16 の非可換版、a は零次のイデアルの元。
使われ方：行列同変版による Lemma A.4 の適用。 -/
def simplicialLemma416Homotopy (I : SimplicialIdealData.{u}) (a : I.ideal (op ⦋0⦌)) (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (simplicialGroupBarMap (I.rightColumnMap a n m)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (simplicialGroupBarMap (simplicialGroupTrivialMap (I.columnGroup n)
        (I.triangularGroup n (m + 1))))) m :=
  diagonalGroupMHomotopy (fun k ↦ lemma416Homotopy n (I.ideal k) (I.vertexElement a k) m)
    (fun {k l} φ ↦ lemma416Homotopy_functorial n (I.ideal k) (I.ideal l)
      (I.ambient.map φ).hom (I.map_mem φ) (I.vertexElement a k) (I.vertexElement a l)
      (I.vertexElement_natural a φ) m)

end SerrePositivity.KST.ProExcision
