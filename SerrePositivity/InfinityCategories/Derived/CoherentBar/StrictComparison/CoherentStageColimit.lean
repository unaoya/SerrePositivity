module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStages
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FilteredModuleUnion
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
概要：実正規化 coherent bar は単体次元の実部分複体の合併である。
方針：包含の単射性と有限 support による網羅性を各次数で判定する。
規約：元の非有界複体と全高次 HA 成分を保持する。
使われ方：filtered 完全性を単体次元のフィルトレーションへ適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarNormalizedStagesDiagram (x : D) : ℕ ⥤ Complex R where
  obj n := dgCoherentBarNormalizedStageComplex R D G x n
  map f := dgCoherentBarNormalizedStageMap R D G x (leOfHom f)
  map_id _ := by ext q; rfl
  map_comp _ _ := by ext q; rfl

def dgCoherentBarNormalizedStagesCocone (x : D) :
    Cocone (dgCoherentBarNormalizedStagesDiagram R D G x) where
  pt := (dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)
  ι :=
    { app n := dgCoherentBarNormalizedStageInclusion R D G x n
      naturality _ _ f := by
        simpa only [dgCoherentBarNormalizedStagesDiagram,
          Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using!
          dgCoherentBarNormalizedStageMap_inclusion R D G x (leOfHom f) }

def dgCoherentBarNormalizedStagesIsColimit (x : D) :
    IsColimit (dgCoherentBarNormalizedStagesCocone R D G x) := by
  apply HomologicalComplex.isColimitOfEval
  intro q
  letI := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (forget (ModuleCat.{u} R))
  exact dgBarFilteredModuleUnionIsColimit R _ _
    (fun _ => Subtype.val_injective)
    (dgCoherentBarNormalizedStages_exhaustive R D G x q)

end SerrePositivity.InfinityCategories
