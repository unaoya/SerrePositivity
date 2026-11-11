module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionEndpointPathFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTriangleHomotopy

/-!
概要：実終点円柱の長辺の全次数の Hom 写像を元の精密化の Yoneda 射へ戻す。
方針：path 関手の因子化に nerve を取り、標準単体との同型を介する。
規約：一単体での一致に限定せず、単体的集合の射そのものを比較する。
使われ方：標準の反転 Hom 比較と実 coslice 終点辺の全座標の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の指定精密化の関手の nerve は同じ精密化の Yoneda 射。 -/
lemma coherentTriangleRefinementFunctor_nerve :
    nerveMap coherentTriangleRefinementFunctor.{u} =
      (stdSimplex.isoNerve 1).inv ≫
        SSet.yonedaEquiv.symm (ComposableArrows.mk₁ coherentTriangleRefinement) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun j ↦ ?_)
  rfl

/-- 実終点円柱の長辺の Hom 写像は元の精密化を反転最小点で評価する射。 -/
lemma coherentCompositionEndpoint_hom_zero_two
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    (coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
      (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2))).map
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ =
      nerveMap (pathFirstMinimumReverseFunctor (1 : Fin 2)) ≫
        (stdSimplex.isoNerve 1).inv ≫ SSet.yonedaEquiv.symm (coherentTriangleHomotopy s) := by
  change nerveMap
    (coherentPrefixPathDeformationFunctor coherentCompositionEndpointObjects
      coherentCompositionEndpointTime (ULift.up 0) (ULift.up 2) ⋙
        coherentPathDeformationFunctor coherentCompositionTetrahedronObjects
          coherentCompositionTetrahedronTime _ _) ≫ s.map _ _ = _
  rw [coherentCompositionEndpoint_path_functor]
  change (nerveMap (pathFirstMinimumReverseFunctor (1 : Fin 2)) ≫
    nerveMap coherentTriangleRefinementFunctor) ≫ s.map _ _ = _
  rw [coherentTriangleRefinementFunctor_nerve, Category.assoc, Category.assoc]
  congr 2
  exact SSet.yonedaEquiv_symm_comp _ _

end SerrePositivity.InfinityCategories.F2
