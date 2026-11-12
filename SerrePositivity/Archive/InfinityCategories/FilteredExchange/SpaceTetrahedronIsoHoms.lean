module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTetrahedronIsos
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom

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
lemma spaceInfinityTetrahedronIso013_hom (s : SpaceInfinity.{u} _⦋3⦌) :
    (spaceInfinityTetrahedronIso013 s).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (spaceInfinityTetrahedronTriangle013 s).toTruncated := by
  exact functorIsoOfEq_hom_simplex _ _ _ _ _ _ (spaceInfinityTriangleIso_hom _)
/-- 概要：面 023 の同型の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma spaceInfinityTetrahedronIso023_hom (s : SpaceInfinity.{u} _⦋3⦌) :
    (spaceInfinityTetrahedronIso023 s).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (spaceInfinityTetrahedronTriangle023 s).toTruncated := by
  exact functorIsoOfEq_hom_simplex _ _ _ _ _ _ (spaceInfinityTriangleIso_hom _)
/-- 概要：面 012 の同型の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma spaceInfinityTetrahedronIso012_hom (s : SpaceInfinity.{u} _⦋3⦌) :
    (spaceInfinityTetrahedronIso012 s).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (spaceInfinityTetrahedronTriangle012 s).toTruncated := by
  exact functorIsoOfEq_hom _ _ _ _ (spaceInfinityTriangleIso_hom _)
/-- 概要：面 123 の同型の前合成の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma spaceInfinityTetrahedronPre123_hom (s : SpaceInfinity.{u} _⦋3⦌) :
    ((spaceInfinityTriangleIso (SpaceInfinity.δ 0 s)).precomp
      (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
        spaceInfinityTetrahedron01 s)).hom =
      SSet.Truncated.HomotopyCategory.homMk (spaceInfinityTetrahedronPre123 s).toTruncated := by
  have h : ((spaceInfinityTriangleIso (SpaceInfinity.δ 0 s)).precomp
      (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
        spaceInfinityTetrahedron01 s)).hom = SSet.Truncated.HomotopyCategory.homMk
      (spaceInfinityTetrahedronPre123Native s).toTruncated := by
    rw [functorIso_precomp_hom, spaceInfinityTriangleIso_hom]
    rfl
  exact h.trans (edgeOfSimplexWithEndpoints_homMk _ _ _ rfl rfl).symm
/-- 概要：面 012 の同型の後合成の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma spaceInfinityTetrahedronPost012_hom (s : SpaceInfinity.{u} _⦋3⦌) :
    ((spaceInfinityTetrahedronIso012 s).postcomp (spaceInfinityTetrahedron23 s)).hom =
      SSet.Truncated.HomotopyCategory.homMk (spaceInfinityTetrahedronPost012 s).toTruncated := by
  have h : ((spaceInfinityTetrahedronIso012 s).postcomp
      (spaceInfinityTetrahedron23 s)).hom = SSet.Truncated.HomotopyCategory.homMk
      (spaceInfinityTetrahedronPost012Native s).toTruncated := by
    rw [functorIso_postcomp_hom, spaceInfinityTetrahedronIso012_hom]
    rfl
  exact h.trans (edgeOfSimplexWithEndpoints_homMk _ _ _ rfl rfl).symm

end SerrePositivity.InfinityCategories.F2
