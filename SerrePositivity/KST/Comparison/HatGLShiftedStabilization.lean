module

public import SerrePositivity.KST.Comparison.HatGLShiftedEntry
public import SerrePositivity.KST.Comparison.CoefficientMatrixStabilization

/-!
# ĜL の安定化と零基点の係数評価

概要：単位を引く係数評価は安定化で既存の係数を保ち、新しい係数を零へ送る。
方針：単位とのブロック和と零の行・列の安定化の差の式を使う。
規約：KST Lemma 2.13 の高次の行列公式の自然性。
使われ方：有限 rank の群同型を図式の自然同型へまとめる。
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
概要：有限 rank の ĜL の安定化の台単体集合の射。
方針：既存の単体的モノイドの射を忘却する。
規約：単位基点を保つ。
使われ方：正次数の群の安定化の基礎射。
-/
def hatGLSpaceStabilization (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    hatGLSpace A r ⟶ hatGLSpace A (r + 1) :=
  Functor.whiskerRight (hatGLStabilization A r) (forget MonCat)

/--
概要：ĜL の安定化は単位基点を保つ。
方針：モノイド準同型の単位保存を使う。
規約：零次の基点の厳密な等式。
使われ方：K-L9 の誘導準同型への入力。
-/
theorem hatGLSpaceStabilization_unit (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    (hatGLSpaceStabilization A r).app (op ⦋0⦌) (1 : hatGLSubmonoid A r 0) =
      (1 : hatGLSubmonoid A (r + 1) 0) :=
  map_one (hatGLStabilizationAt A r 0)

/--
概要：安定化後の零基点の係数写像は既存の係数写像、または新しい零の定数写像である。
方針：各単体次数のブロックの差を計算し、四つの添字の場合に分ける。
規約：新しい行・列の係数の正次数の類は群の単位となる。
使われ方：係数群の行列の安定化との可換性。
-/
theorem hatGLShiftedEntryMap_stabilization (A : SimplicialObject RingCat.{u}) (r : ℕ)
    (i j : Fin r ⊕ Fin 1) :
    hatGLSpaceStabilization A r ≫
        hatGLShiftedEntryMap A (r + 1) (finSumFinEquiv i) (finSumFinEquiv j) =
      match i, j with
      | Sum.inl i, Sum.inl j => hatGLShiftedEntryMap A r i j
      | _, _ => SSet.const (X := hatGLSpace A r) (0 : A.obj (op ⦋0⦌)) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro a
  calc
    _ = (matrixStabilization (A.obj d) r a.val - 1) (finSumFinEquiv i) (finSumFinEquiv j) :=
      hatGLShiftedEntryMap_app A (r + 1) d.unop.len
        (hatGLStabilizationAt A r d.unop.len a) _ _
    _ = (matrixZeroStabilization (A.obj d) r (a.val - 1))
        (finSumFinEquiv i) (finSumFinEquiv j) :=
      congrArg (fun b => b (finSumFinEquiv i) (finSumFinEquiv j))
        (matrixStabilization_sub_one (A.obj d) r a.val)
    _ = _ := by
      cases i <;> cases j <;>
        simp [matrixZeroStabilization, Matrix.reindex_apply, Matrix.fromBlocks,
          SSet.const, ringSpace]
      exact (hatGLShiftedEntryMap_app A r d.unop.len a _ _).symm

end SerrePositivity.KST.Comparison
