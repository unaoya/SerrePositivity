module

public import SerrePositivity.KST.Comparison.StableHatGLKan

/-!
# 群状モノイドの正次数の delooping の群同型

概要：Kan な群状モノイドの正次数の群は分類空間の一つ上の群と同型である。
方針：標準群完備化の点付き射の局所化可逆性を群同型へ渡し、K-L9 の loop の次数移動と合成する。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13。既存の群演算との整合を含む。
使われ方：安定 ĜL の分類空間の高次の群の具体的な表示。
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
概要：標準群完備化写像を単位基点の点付き射として束ねる。
方針：全次数の単位を定数ループへ送る既証明の式を使う。
規約：標準写像を選び直さない。
使われ方：K-L9 の正次数の誘導準同型への入力。
-/
def monoidGroupCompletionPointedMap (M : SimplicialObject MonCat.{u}) :
    monoidPointed M ⟶ monoidGroupCompletionSpace M :=
  Under.homMk (monoidGroupCompletionMap M) (monoidGroupCompletionMap_unit M)

/--
概要：点付き局所化同型は既存の正次数の群の同型を誘導する。
方針：全基点の全単射性を基点保存の等式で移し、誘導準同型と合わせる。
規約：添字 n は実際の次数 n+1。
使われ方：標準群完備化比較を群としての次数移動へ渡す。
-/
def pointedKanPositiveHomotopyMulEquiv {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right n X.basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n Y.basepoint := by
  let hb := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f
  have hπ := kanPiIsomorphism_of_localized_isIso f.right hf
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr (n + 1) f.right rfl hb rfl hb
    (hπ X.basepoint (n + 1))
  exact MulEquiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f.right hb) hh

/--
概要：Kan な群状モノイドの正次数の群と分類空間の一つ上の群の同型。
方針：標準群完備化写像の群同型と K-L9 の正次数の loop の同型を合成する。
規約：元の成分群の積との向きの問題は基本群の比較で別に処理済み。
使われ方：KST Lemma 2.13 の i>1 の delooping の部分。
-/
def monoidBarPositiveHomotopyMulEquiv (M : SimplicialObject MonCat.{u})
    [KanComplex (monoidSpace M)] (hM : SimplicialMonoid.IsGrouplike M) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidSpace M) n (monoidPointed M).basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidBarKanPointed M).right (n + 1)
        (monoidBarKanPointed M).basepoint := by
  letI : KanComplex (monoidPointed M).right :=
    inferInstanceAs (KanComplex (monoidSpace M))
  exact (pointedKanPositiveHomotopyMulEquiv (monoidGroupCompletionPointedMap M)
    (monoidGroupCompletionMap_localized_isIso M hM) n).trans
      (Spectra.loopPositiveHomotopyEquiv (monoidBarKanPointed M) n)

/--
概要：安定 ĜL の正次数の群と BĜL の一つ上の群の同型。
方針：安定モノイドの実際の Kan 性と群状性を一般の比較へ供給する。
規約：KST Lemma 2.13 の安定 rank の delooping。追加仮定は無い。
使われ方：安定係数行列群の具体的な同定との合成。
-/
def stableHatGLBarPositiveHomotopyMulEquiv (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidSpace (stableHatGL A)) n
        (monoidPointed (stableHatGL A)).basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidBarKanPointed (stableHatGL A)).right (n + 1)
        (monoidBarKanPointed (stableHatGL A)).basepoint :=
  monoidBarPositiveHomotopyMulEquiv (stableHatGL A) (stableHatGL_isGrouplike A) n

end SerrePositivity.KST.Comparison
