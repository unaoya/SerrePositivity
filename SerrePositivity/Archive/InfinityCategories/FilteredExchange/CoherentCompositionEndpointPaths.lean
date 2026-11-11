module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixConeSimplex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedron
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTrianglePathSets

/-!
概要：零面の実 coslice 円柱の終点に現れる精密化の二端点を元の path へ戻す。
方針：対象 (0,3,3) と時刻 (0,0,1) の prefix 変形を元の三単体へ代入する。
規約：元の長辺と二辺合成の path を実際の等式で保持する。
使われ方：指定比較円柱の終点像と元の指定精密化の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 終点円柱の対象写像 (0,3,3)。 -/
def coherentCompositionEndpointObjects : ULift.{u} (Fin 3) →o ULift.{u} (Fin 4) :=
  (prependOrderHom (OrderHom.const (Fin 2) (2 : Fin 3))).uliftMap

/-- 終点円柱の時刻 (0,0,1)。 -/
def coherentCompositionEndpointTime : ULift.{u} (Fin 3) →o Fin 2 :=
  (coherentPrefixConeTime (OrderHom.id (α := Fin 2))).comp
    ⟨ULift.down, fun _ _ h ↦ h⟩

/-- 終点円柱の長辺 path の像は元の三角形の長辺 path。 -/
lemma coherentCompositionEndpoint_path_source :
    coherentPathDeformation coherentCompositionTetrahedronObjects
      coherentCompositionTetrahedronTime
        (coherentPrefixPathDeformation coherentCompositionEndpointObjects
          coherentCompositionEndpointTime coherentTrianglePath02.{u}) =
      coherentTrianglePath02 := by
  apply SimplicialThickening.Path.ext
  ext z
  rcases z with ⟨z⟩
  fin_cases z <;>
    simp only [coherentPathDeformation, coherentPrefixPathDeformation,
      coherentTrianglePath02_set, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff,
      ULift.exists, Fin.exists_fin_succ, Fin.exists_fin_zero] <;>
    simp [coherentCompositionEndpointObjects, coherentCompositionEndpointTime,
      coherentPrefixConeTime, prependOrderHom, coherentCompositionTetrahedronObjects,
      coherentCompositionTetrahedronTime, coherentTriangleDeformationTime,
      OrderHom.uliftMap, Fin.cases] <;> decide

/-- 終点円柱の合成 path の像は元の三角形の二辺合成 path。 -/
lemma coherentCompositionEndpoint_path_target :
    coherentPathDeformation coherentCompositionTetrahedronObjects
      coherentCompositionTetrahedronTime
        (coherentPrefixPathDeformation coherentCompositionEndpointObjects
          coherentCompositionEndpointTime coherentTriangleCompositePath.{u}) =
      coherentTriangleCompositePath := by
  apply SimplicialThickening.Path.ext
  ext z
  rcases z with ⟨z⟩
  fin_cases z <;>
    simp only [coherentPathDeformation, coherentPrefixPathDeformation,
      coherentTriangleCompositePath_set, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff,
      ULift.exists, Fin.exists_fin_succ, Fin.exists_fin_zero] <;>
    simp [coherentCompositionEndpointObjects, coherentCompositionEndpointTime,
      coherentPrefixConeTime, prependOrderHom, coherentCompositionTetrahedronObjects,
      coherentCompositionTetrahedronTime, coherentTriangleDeformationTime,
      OrderHom.uliftMap, Fin.cases] <;> decide

end SerrePositivity.InfinityCategories.F2
