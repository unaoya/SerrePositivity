module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTetrahedronIsos
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerHom

/-!
概要：四面の指定関手同型と元の辺の類の対応。
方針：両端の輸送と前後合成が指定辺の類を保つことを使う。
規約：四隅を共通の六関手で表す。
使われ方：四面の関手同型の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：面 013 の同型の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronIso013_hom (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronIso013 s).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (catInfinityTetrahedronTriangle013 s).toTruncated := by
  exact functorIsoOfEq_hom_simplex _ _ _ _ _ _ (catInfinityTriangleIso_hom _)
/-- 概要：面 023 の同型の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronIso023_hom (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronIso023 s).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (catInfinityTetrahedronTriangle023 s).toTruncated := by
  exact functorIsoOfEq_hom_simplex _ _ _ _ _ _ (catInfinityTriangleIso_hom _)
/-- 概要：面 012 の同型の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronIso012_hom (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronIso012 s).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (catInfinityTetrahedronTriangle012 s).toTruncated := by
  exact functorIsoOfEq_hom _ _ _ _ (catInfinityTriangleIso_hom _)
/-- 概要：面 123 の同型の前合成の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronPre123_hom (s : CatInfinity.{u} _⦋3⦌) :
    ((catInfinityTriangleIso (CatInfinity.δ 0 s)).precomp
      (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
        catInfinityTetrahedron01 s)).hom =
      SSet.Truncated.HomotopyCategory.homMk (catInfinityTetrahedronPre123 s).toTruncated := by
  have h : ((catInfinityTriangleIso (CatInfinity.δ 0 s)).precomp
      (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
        catInfinityTetrahedron01 s)).hom = SSet.Truncated.HomotopyCategory.homMk
      (catInfinityTetrahedronPre123Native s).toTruncated := by
    rw [functorIso_precomp_hom, catInfinityTriangleIso_hom]
    rfl
  exact h.trans (edgeOfSimplexWithEndpoints_homMk _ _ _ rfl rfl).symm
/-- 概要：面 012 の同型の後合成の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronPost012_hom (s : CatInfinity.{u} _⦋3⦌) :
    ((catInfinityTetrahedronIso012 s).postcomp (catInfinityTetrahedron23 s)).hom =
      SSet.Truncated.HomotopyCategory.homMk (catInfinityTetrahedronPost012 s).toTruncated := by
  have h : ((catInfinityTetrahedronIso012 s).postcomp
      (catInfinityTetrahedron23 s)).hom = SSet.Truncated.HomotopyCategory.homMk
      (catInfinityTetrahedronPost012Native s).toTruncated := by
    rw [functorIso_postcomp_hom, catInfinityTetrahedronIso012_hom]
    rfl
  exact h.trans (edgeOfSimplexWithEndpoints_homMk _ _ _ rfl rfl).symm

end SerrePositivity.InfinityCategories.F2
