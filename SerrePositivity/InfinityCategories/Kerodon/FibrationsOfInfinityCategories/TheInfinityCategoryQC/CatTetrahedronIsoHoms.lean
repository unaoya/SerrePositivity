module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatTetrahedronIsos
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom

/-!
概要：四面の指定関手同型と元の辺の類の対応。
方針：両端の輸送と前後合成が指定辺の類を保つことを使う。
規約：四隅を共通の六関手で表す。
使われ方：四面の関手同型の合成則。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：面 013 の同型の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronIso013_hom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronIso013 s).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronTriangle013 s).toTruncated := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_hom_simplex _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso_hom _)
/-- 概要：面 023 の同型の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronIso023_hom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronIso023 s).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronTriangle023 s).toTruncated := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_hom_simplex _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso_hom _)
/-- 概要：面 012 の同型の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronIso012_hom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronIso012 s).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronTriangle012 s).toTruncated := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_hom _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso_hom _)
/-- 概要：面 123 の同型の前合成の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronPre123_hom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 s)).precomp
      (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedron01 s)).hom =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronPre123 s).toTruncated := by
  have h : ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 s)).precomp
      (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedron01 s)).hom = SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronPre123Native s).toTruncated := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso_hom]
    rfl
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeOfSimplexWithEndpoints_homMk _ _ _ rfl rfl).symm
/-- 概要：面 012 の同型の後合成の順方向の射は対応する指定辺の類。
方針：同型の輸送または前後合成の射の計算を使う。
規約：元の三角形の辺の類を保持する。
使われ方：四面の同型の合成を指定辺の正方形で比較する。 -/
lemma catInfinityTetrahedronPost012_hom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronIso012 s).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedron23 s)).hom =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronPost012 s).toTruncated := by
  have h : ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronIso012 s).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedron23 s)).hom = SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronPost012Native s).toTruncated := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, catInfinityTetrahedronIso012_hom]
    rfl
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeOfSimplexWithEndpoints_homMk _ _ _ rfl rfl).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
