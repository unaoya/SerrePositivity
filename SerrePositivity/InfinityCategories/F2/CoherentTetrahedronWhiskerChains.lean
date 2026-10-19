module

public import SerrePositivity.InfinityCategories.F2.CoherentTetrahedronWhiskerPathSets

/-!
概要：両端の射を合成した面の精密化の辺。
方針：精密化の像と豊穣関手の合成の保存を一次単体で照合する。
規約：元の一単体を別の代表へ変更しない。
使われ方：Cat_∞ の三単体の四面の指定関手同型の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：面 123 の精密化を 01 と合成すると中間点 2 を加える辺。
方針：両端の path と射の一意性を使う。
規約：元の一単体の厳密な等式。
使われ方：四面の合成則を同じ Hom で比較する。 -/
lemma coherentTetrahedronWhisker013_chain :
    (nerveMap (coherentTetrahedronFace123.{u} ⋙ coherentTetrahedronWhisker01)).app
        (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ coherentTriangleRefinement) =
      ComposableArrows.mk₁ coherentTetrahedronRefine013Full := by
  refine ComposableArrows.ext₁ coherentTetrahedronWhisker013_short
    coherentTetrahedronWhisker013_long ?_
  exact coherentPathHom_ext _ _
/-- 概要：面 012 の精密化を 23 と合成すると中間点 1 を加える辺。
方針：両端の path と射の一意性を使う。
規約：元の一単体の厳密な等式。
使われ方：四面の合成則を同じ Hom で比較する。 -/
lemma coherentTetrahedronWhisker023_chain :
    (nerveMap (coherentTetrahedronFace012.{u} ⋙ coherentTetrahedronWhisker23)).app
        (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ coherentTriangleRefinement) =
      ComposableArrows.mk₁ coherentTetrahedronRefine023Full := by
  refine ComposableArrows.ext₁ coherentTetrahedronWhisker023_short
    coherentTetrahedronWhisker023_long ?_
  exact coherentPathHom_ext _ _

end SerrePositivity.InfinityCategories.F2
