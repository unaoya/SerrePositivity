module
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat


/-!
概要：同じ一単体を持つ辺の正方形の端点の輸送。
方針：四頂点の等式を同時に消去し、辺の外延性を使う。
規約：可換性はホモトピー圏での合成の等式。
使われ方：錐の脚の正方形を coherent な関手の正方形にする。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：四頂点を同時に輸送しても同じ一単体の正方形の可換性は保たれる。
方針：頂点の等式を消去して四本の辺を外延性で同定する。
規約：各辺の両端の型が異なる表示を許す。
使われ方：Cat_∞ の比較の正方形を指定関手の式へ移す。 -/
lemma homMk_square_transport {X : SSet.{u}} {a b c d a' b' c' d' : X _⦋0⦌}
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
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (he : e.edge = e'.edge) (hr : r.edge = r'.edge)
    (hl : l.edge = l'.edge) (hf : f.edge = f'.edge) :
    SSet.Truncated.HomotopyCategory.homMk e' ≫ SSet.Truncated.HomotopyCategory.homMk r' =
      SSet.Truncated.HomotopyCategory.homMk l' ≫ SSet.Truncated.HomotopyCategory.homMk f' := by
  subst a'
  subst b'
  subst c'
  subst d'
  have he' : e = e' := by apply SSet.Truncated.Edge.ext; exact he
  have hr' : r = r' := by apply SSet.Truncated.Edge.ext; exact hr
  have hl' : l = l' := by apply SSet.Truncated.Edge.ext; exact hl
  have hf' : f = f' := by apply SSet.Truncated.Edge.ext; exact hf
  simpa only [← he', ← hr', ← hl', ← hf'] using h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
