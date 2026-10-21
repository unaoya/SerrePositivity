module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondCompositeProjection
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleHomSecond
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerCancellation

/-!
概要：元の大域 Hom 作用上で、第二面の比較を同じ分解三角形の指定合成比較へ戻す。
方針：二つの三角形の同じ第二面作用を照合し、指定同型の前合成の回収則を使う。
規約：元の全相対 Hom と元の第二面の指定同型を保持する。
使われ方：共有頂点の三角形の第二面を二回目の自然性と結合比較へ分解する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全 Hom から第二面へ進む二つの同じ三角形作用は厳密に一致する。 -/
lemma cocartesianBaseChangeSecondTriangleHomComparison_decomposition :
    cocartesianBaseChangeSecondTriangleHomComparison l k p q ≫
        cocartesianBaseChangeSecondTriangleHomLong l k p q =
      cocartesianBaseChangeTriangleHomComparison l k p q ≫
        cocartesianBaseChangeTriangleHomSecond l k p q := by
  rw [cocartesianBaseChangeSecondTriangleHomComparison_long,
    cocartesianBaseChangeTriangleHomComparison_second]
  rfl

/-- 同じ元の大域 Hom 上で、第二面の輸送比較は指定された分解三角形の合成比較になる。 -/
lemma cocartesianBaseChangeSecondHomCompositeTransportIso_naturality_heq :
    HEq ((cocartesianBaseChangeSecondHomCompositeTransportIso l k p q).precomp
      (cocartesianBaseChangeTriangleHomComparison l k p q ≫
        cocartesianBaseChangeTriangleHomSecond l k p q))
      ((cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q).precomp
        (cocartesianBaseChangeSecondTriangleHomComparison l k p q)) := by
  have h := cocartesianBaseChangeSecondHomCompositeTransportIso_projection_precomp_heq
    l k p q (cocartesianBaseChangeSecondTriangleHomComparison l k p q)
  exact (F2.functorIso_precomp_heq_of_map_eq
    (cocartesianBaseChangeSecondHomCompositeTransportIso l k p q)
    (cocartesianBaseChangeSecondTriangleHomComparison_decomposition l k p q).symm).trans h

end SerrePositivity.InfinityCategories
