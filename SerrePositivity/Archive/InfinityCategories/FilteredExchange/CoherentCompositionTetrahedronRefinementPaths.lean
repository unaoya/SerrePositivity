module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedron
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTrianglePathSets

/-!
概要：比較三単体の第二面の二つの長い path を元の精密化の両端に同定する。
方針：対象 (0,0,2) と時刻 (0,1,1) を集合表示で計算する。
規約：元の長辺 path と元の二辺合成 path をそのまま使う。
使われ方：第二面が元の指定された Hom の辺を保持することの証明。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 第二面の対象写像 (0,0,2)。 -/
def coherentCompositionTetrahedronRefinementObjects :
    ULift.{u} (Fin 3) →o ULift.{u} (Fin 3) :=
  coherentCompositionTetrahedronObjects.comp
    (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap

/-- 第二面の時刻 (0,1,1)。 -/
def coherentCompositionTetrahedronRefinementTime : ULift.{u} (Fin 3) →o Fin 2 :=
  coherentCompositionTetrahedronTime.{u}.comp
    (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap

local notation "A" => coherentCompositionTetrahedronRefinementObjects
local notation "t" => coherentCompositionTetrahedronRefinementTime

/-- 第二面の長辺 path は元の三角形の長辺 path。 -/
lemma coherentCompositionTetrahedron_refinement_source :
    coherentPathDeformation A t coherentTrianglePath02.{u} = coherentTrianglePath02 := by
  apply SimplicialThickening.Path.ext
  ext z
  rcases z with ⟨z⟩
  fin_cases z <;>
    simp only [coherentPathDeformation, coherentCompositionTetrahedronRefinementObjects,
      coherentCompositionTetrahedronRefinementTime, coherentTrianglePath02_set,
      coherentCompositionTetrahedronObjects, coherentCompositionTetrahedronTime,
      coherentTriangleDeformationTime, Set.mem_union, Set.mem_ofPred_eq,
      Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left] <;> decide

/-- 第二面の合成 path は元の三角形の二辺合成 path。 -/
lemma coherentCompositionTetrahedron_refinement_target :
    coherentPathDeformation A t coherentTriangleCompositePath.{u} =
      coherentTriangleCompositePath := by
  apply SimplicialThickening.Path.ext
  ext z
  rcases z with ⟨z⟩
  fin_cases z <;>
    simp only [coherentPathDeformation, coherentCompositionTetrahedronRefinementObjects,
      coherentCompositionTetrahedronRefinementTime, coherentTriangleCompositePath_set,
      coherentCompositionTetrahedronObjects, coherentCompositionTetrahedronTime,
      coherentTriangleDeformationTime, Set.mem_union, Set.mem_ofPred_eq,
      Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left] <;> decide

end SerrePositivity.InfinityCategories.F2
