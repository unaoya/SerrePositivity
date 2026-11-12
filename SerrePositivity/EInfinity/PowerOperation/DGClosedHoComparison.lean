module

public import SerrePositivity.EInfinity.PowerOperation.OrdinaryNerveHomotopyFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedRoofRefinements
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyCategory
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge

/-!
# 閉零圏の同じ通常射と native dg nerve のホモトピー圏の比較

DAG XIII §2.2 の π/H の全射の自然性の補助。元の閉射の辺を同じ H⁰ の商へ戻す。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

def dgClosedHoFunctor : ClosedCategory A D ⥤ hoFunctor.obj (dgNerve A D) :=
  ordinaryNerveHomotopyFunctor (ClosedCategory A D) ⋙
    (hoFunctor.map (closedNerveInclusion A D)).toFunctor

def dgNativeHoH0Equivalence : hoFunctor.obj (dgNerve A D) ≌
    DifferentialGraded.HomotopyCategory A D :=
  (homotopyCategoryBridge (dgNerve A D)).symm.trans (DifferentialGradedCategories.equivalence A D)

lemma dgClosedHoFunctor_comp_H0 :
    dgClosedHoFunctor A D ⋙ (dgNativeHoH0Equivalence A D).functor = toHomotopy A D := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (toH0 A D).map
    ((pathToEdgeHomotopyCategory ((truncation 2).obj (dgNerve A D))).map
      (SSet.HomotopyCategory.homMk ((nerve.edgeMk f).map (closedNerveInclusion A D)))) = _
  let e := ((nerve.edgeMk f).map (closedNerveInclusion A D)).toTruncated
  have hp : (pathToEdgeHomotopyCategory ((truncation 2).obj (dgNerve A D))).map
      (SSet.Truncated.HomotopyCategory.homMk e) = SSet.Truncated.HomotopyCategory₂.homMk e :=
    SSet.Truncated.HomotopyCategory.lift_map_homMk _ _ _ _ e
  change (toH0 A D).map ((pathToEdgeHomotopyCategory _).map
    (SSet.Truncated.HomotopyCategory.homMk e)) = _
  rw [hp, toH0_homMk]
  apply congrArg (toHomotopy A D).map
  apply (closedHomEquiv A D X Y).injective
  exact (SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle e).trans rfl

end SerrePositivity.EInfinity.PowerOperation
