module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.EdgeSquareTransport

/-!
概要：四辺の一次単体の一致による正方形の輸送。
方針：端点の等式を各辺の面から回収する。
規約：四頂点の等式を呼び出し側に要求しない。
使われ方：coherent 三単体の大きな境界定義を展開せずに合成関係を移す。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：四辺が同じ一次単体ならホモトピー圏の正方形の可換性を移せる。
方針：端点を面写像で同定し、四頂点を同時に輸送する。
規約：両端点の表示が異なる二組の四辺を比較する。
使われ方：Cat_∞ の四面の合成則の端点の正規化。 -/
lemma homMk_square_of_edge_eq {X : SSet.{u}} {a b c d a' b' c' d' : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) a b)
    (r : SSet.Truncated.Edge (X := (truncation 2).obj X) b d)
    (l : SSet.Truncated.Edge (X := (truncation 2).obj X) a c)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) c d)
    (e' : SSet.Truncated.Edge (X := (truncation 2).obj X) a' b')
    (r' : SSet.Truncated.Edge (X := (truncation 2).obj X) b' d')
    (l' : SSet.Truncated.Edge (X := (truncation 2).obj X) a' c')
    (f' : SSet.Truncated.Edge (X := (truncation 2).obj X) c' d')
    (h : SSet.Truncated.HomotopyCategory.homMk e ≫ SSet.Truncated.HomotopyCategory.homMk r =
      SSet.Truncated.HomotopyCategory.homMk l ≫ SSet.Truncated.HomotopyCategory.homMk f)
    (he : e.edge = e'.edge) (hr : r.edge = r'.edge)
    (hl : l.edge = l'.edge) (hf : f.edge = f'.edge) :
    SSet.Truncated.HomotopyCategory.homMk e' ≫ SSet.Truncated.HomotopyCategory.homMk r' =
      SSet.Truncated.HomotopyCategory.homMk l' ≫ SSet.Truncated.HomotopyCategory.homMk f' := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homMk_square_transport e r l f e' r' l' f' h
    (e.src_eq.symm.trans ((congrArg (X.δ 1) he).trans e'.src_eq))
    (e.tgt_eq.symm.trans ((congrArg (X.δ 0) he).trans e'.tgt_eq))
    (l.tgt_eq.symm.trans ((congrArg (X.δ 0) hl).trans l'.tgt_eq))
    (f.tgt_eq.symm.trans ((congrArg (X.δ 0) hf).trans f'.tgt_eq)) he hr hl hf

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
