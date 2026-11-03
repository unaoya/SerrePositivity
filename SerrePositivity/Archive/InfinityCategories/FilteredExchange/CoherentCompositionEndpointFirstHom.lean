module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionEndpointFirstPath
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionEndpointHom
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.WeightedTriangleFirstHom

/-!
概要：実終点円柱の最初の Hom を元の精密化の終点の全次数での評価へ戻す。
方針：二辺合成 path への定値関手を元の精密化の終点への関手に因子化する。
規約：指定精密化と元の対象を保持する。
使われ方：実三角形の全 Hom と標準反転 Hom 比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 実終点円柱の最初の Hom は元の精密化の終点を全次数で評価する射。 -/
lemma coherentCompositionEndpoint_hom_zero_one
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    (coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
      (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2))).map
        ⟨ULift.up 0⟩ ⟨ULift.up 1⟩ =
      nerveMap ((Functor.const (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3))
        (ULift.up 1))).obj (ULift.up (1 : Fin 2))) ≫
        (stdSimplex.isoNerve 1).inv ≫ SSet.yonedaEquiv.symm (coherentTriangleHomotopy s) := by
  change nerveMap
    (coherentPrefixPathDeformationFunctor coherentCompositionEndpointObjects
      coherentCompositionEndpointTime (ULift.up 0) (ULift.up 1) ⋙
        coherentPathDeformationFunctor coherentCompositionTetrahedronObjects
          coherentCompositionTetrahedronTime _ _) ≫ s.map _ _ = _
  rw [coherentCompositionEndpoint_path_first_functor]
  have hf : (Functor.const (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3))
      (ULift.up 1))).obj coherentTriangleCompositePath =
      (Functor.const (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3))
        (ULift.up 1))).obj (ULift.up (1 : Fin 2)) ⋙ coherentTriangleRefinementFunctor := by
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  rw [hf]
  change (nerveMap ((Functor.const (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3))
    (ULift.up 1))).obj (ULift.up (1 : Fin 2))) ≫
      nerveMap coherentTriangleRefinementFunctor) ≫ s.map _ _ = _
  rw [coherentTriangleRefinementFunctor_nerve, Category.assoc, Category.assoc]
  congr 2
  exact SSet.yonedaEquiv_symm_comp _ _

end SerrePositivity.InfinityCategories.F2
