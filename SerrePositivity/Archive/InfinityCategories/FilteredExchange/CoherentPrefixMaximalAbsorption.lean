module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixPathEnriched
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexDeformation

/-!
概要：最大 path 表示を後合成すると、prefix 変形の時刻に依存しない。
方針：同じ二端点間の全区間を両側の support として回収する。
規約：全 path と元の対象写像を保持する。
使われ方：標準図式を固定する零面円柱の射影の証明。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 最大化は任意の prefix 変形の時刻を吸収する。 -/
lemma coherentPrefixPathDeformation_maximal_absorption
    {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j : J} (P : Path i j) :
    coherentPathDeformation OrderHom.id (OrderHom.const K 1)
      (coherentPrefixPathDeformation A t P) =
        coherentPathDeformation A (OrderHom.const J 1) P := by
  apply SimplicialThickening.Path.ext
  rw [coherentPathDeformation_one, coherentPathDeformation_one]
  rfl

/-- 全豊穣 Hom でも最大化は prefix 変形を吸収する。 -/
lemma coherentPrefixPathDeformationEnriched_maximal_absorption
    {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) :
    (coherentPrefixPathDeformationEnriched A t).comp SSet
      (coherentPathDeformationEnriched OrderHom.id (OrderHom.const K 1)) =
        coherentPathDeformationEnriched A (OrderHom.const J 1) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext
    (fun z ↦ coherentPrefixPathDeformation_maximal_absorption A t (P.obj z))

end SerrePositivity.InfinityCategories.F2
