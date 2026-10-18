module
public import SerrePositivity.InfinityCategories.Stable.SuspensionColimitComparison
public import SerrePositivity.InfinityCategories.Stable.SuspensionTranspose

/-! # 同じ span を持つ転置 suspension の交換比較

概要：転置前後で span が等しい suspension の交換同型は、同じ span 上の余極限頂点比較である。
方針：転置した余錐の固定図式を等号で揃え、同じ span の suspension 比較の同定を適用する。
規約：span の等号は仮定として保持する。使われ方：対称な二枝の模型の交換作用を写像空間で読む。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：転置しても span が等しい場合に、転置した余錐を元の span 上に表示する。
方針：固定条件に span の等号を合成する。
規約：余錐の値は変えない。使われ方：同じ coslice 内での交換の標準比較。 -/
def SuspensionSquare.transposedCoconeOfSameSpan {X : SSet.{u}} {x : X _⦋0⦌}
    (s : SuspensionSquare x) (h : pushoutSpan s.transpose.square = pushoutSpan s.square) :
    JoinCocone (pushoutSpan s.square) :=
  ⟨(pushoutCocone s.transpose.square).val, (pushoutCocone s.transpose.square).property.trans h⟩

/-- 概要：span の表示を揃えた転置余錐は余極限余錐である。
方針：余錐の値が同じ場合の余極限性の不変性を使う。
規約：値域の quasicategory 性は不要。使われ方：交換の標準頂点比較の入力。 -/
lemma SuspensionSquare.transposedCoconeOfSameSpan_isColimit {X : SSet.{u}} {x : X _⦋0⦌}
    (s : SuspensionSquare x) (h : pushoutSpan s.transpose.square = pushoutSpan s.square) :
    IsColimitCone (s.transposedCoconeOfSameSpan h) :=
  (isColimitCone_iff_of_val_eq (s.transposedCoconeOfSameSpan h)
    (pushoutCocone s.transpose.square) rfl).2 s.transpose.isPushout

/-- 概要：表示を揃えた転置余錐の四角形表示は転置した suspension である。
方針：元の余錐の値を使い、形状同型とその逆を消す。
規約：関手単体集合の頂点の等号。使われ方：suspension 比較の標準同定への適用。 -/
lemma SuspensionSquare.transposedCoconeOfSameSpan_diagram {X : SSet.{u}} {x : X _⦋0⦌}
    (s : SuspensionSquare x) (h : pushoutSpan s.transpose.square = pushoutSpan s.square) :
    (cosliceSquareDiagramMap (pushoutSpan s.square)).app (Opposite.op ⦋0⦌)
      (s.transposedCoconeOfSameSpan h) = functorVertex s.transpose.square := by
  rw [cosliceSquareDiagramMap_vertex]
  change functorVertex (spanCoconeSquareIso.inv ≫
    (spanCoconeSquareIso.hom ≫ s.transpose.square)) = _
  rw [Iso.inv_hom_id_assoc]

/-- 概要：span が転置で変わらない suspension の swapIso は標準余極限頂点比較に一致する。
方針：元と転置の余錐を同じ coslice に置き、suspension の標準比較との同定を使う。
規約：span の等号を要求する条件付きの同定で、負号はまだ主張しない。
使われ方：対称な二枝の模型での交換作用の写像空間への移行。 -/
lemma SuspensionSquare.swapIso_eq_colimitVertexIso_arrow_of_sameSpan
    {X : SSet.{u}} [Quasicategory X] {x : X _⦋0⦌} (s : SuspensionSquare x)
    (h : pushoutSpan s.transpose.square = pushoutSpan s.square) :
    (Arrow.mk s.swapIso.hom : Arrow (hoFunctor.obj X)) =
      Arrow.mk (colimitVertexIso (pushoutCocone s.square) (s.transposedCoconeOfSameSpan h)
        s.isPushout (s.transposedCoconeOfSameSpan_isColimit h)).hom :=
  s.comparisonIso_eq_colimitVertexIso_arrow s.transpose (pushoutCocone s.square)
    (s.transposedCoconeOfSameSpan h) s.isPushout (s.transposedCoconeOfSameSpan_isColimit h)
      (cosliceSquareDiagramMap_pushoutCocone s.square) (s.transposedCoconeOfSameSpan_diagram h)

end SerrePositivity.InfinityCategories
