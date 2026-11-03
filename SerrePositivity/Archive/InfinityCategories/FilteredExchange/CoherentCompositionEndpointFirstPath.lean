module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionEndpointPathFunctor

/-!
概要：実終点円柱の最初の辺の全 path は元の二辺合成 path に写る。
方針：隣接 path の一意性で台の計算へ還元する。
規約：長辺の指定精密化の終点を同じ実 path として保持する。
使われ方：実三角形と標準反転 Hom 比較の最初の Hom の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 最初の隣接 path は元の三角形の二辺合成 path に写る。 -/
lemma coherentCompositionEndpoint_path_first :
    coherentPathDeformation coherentCompositionTetrahedronObjects
      coherentCompositionTetrahedronTime
        (coherentPrefixPathDeformation coherentCompositionEndpointObjects
          coherentCompositionEndpointTime coherentTrianglePath01.{u}) =
      coherentTriangleCompositePath := by
  apply SimplicialThickening.Path.ext
  ext z
  rcases z with ⟨z⟩
  fin_cases z <;>
    simp only [coherentPathDeformation, coherentPrefixPathDeformation,
      coherentTrianglePath01_set, coherentTriangleCompositePath_set,
      Set.mem_union, Set.mem_image, Set.mem_ofPred_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff,
      ULift.exists, Fin.exists_fin_succ, Fin.exists_fin_zero] <;>
    simp [coherentCompositionEndpointObjects, coherentCompositionEndpointTime,
      coherentPrefixConeTime, prependOrderHom, coherentCompositionTetrahedronObjects,
      coherentCompositionTetrahedronTime, coherentTriangleDeformationTime,
      OrderHom.uliftMap, Fin.cases] <;> decide

/-- 実終点円柱の最初の辺の全 path 関手は元の二辺合成 path への定値関手。 -/
lemma coherentCompositionEndpoint_path_first_functor :
    coherentPrefixPathDeformationFunctor coherentCompositionEndpointObjects
      coherentCompositionEndpointTime (ULift.up 0) (ULift.up 1) ⋙
        coherentPathDeformationFunctor coherentCompositionTetrahedronObjects
          coherentCompositionTetrahedronTime _ _ =
      (Functor.const (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3))
        (ULift.up 1))).obj coherentTriangleCompositePath := by
  apply CategoryTheory.Functor.ext (fun P ↦ ?_)
  rw [coherentTrianglePath01_unique P]
  exact coherentCompositionEndpoint_path_first

end SerrePositivity.InfinityCategories.F2
