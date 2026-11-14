module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarColumnNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarGradedFunctor
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDegreeCofan

/-!
概要：元のbarと直和全複体を結ぶ次数別の余積の脚を、元の自然変換に自然にする。
方針：同じ比較列のシフトを展開し、シフト前の列の自然性へ戻す。
規約：同じ符号規約・同じ全複体比較を保持する。
使われ方：3b-3 R6、実非正規化barの関手が元の各因子の射を保つことの照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SSet HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 次数別の同じ比較余積の脚は、元の自然変換を同じシフトで写した射に自然。 -/
lemma smallStrictBarDegreeCofan_naturality
    {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) (q : ℤ)
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    (smallStrictBarDegreeCofan A F q).inj s ≫
        ((strictBarTotalComplexFunctor A J).map η).f q =
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map
        ((moduleShiftFunctor A PUnit.{1} (s.1 : ℤ)).map (η.app (s.2.down.obj 0)))).f q ≫
        (smallStrictBarDegreeCofan A G q).inj s := by
  change (((moduleHomπ A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
      (smallStrictBarTotalTarget A F) PUnit.unit).f 0 (smallStrictBarTotalColumn A F s)).v
        q q (add_zero q)) ≫ _ = _
  change _ = _ ≫ (((moduleHomπ A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A G) s))
      (smallStrictBarTotalTarget A G) PUnit.unit).f 0 (smallStrictBarTotalColumn A G s)).v
        q q (add_zero q))
  rw [smallStrictBarTotalColumn_point, smallStrictBarTotalColumn_point,
    unsignedLeftShift_v, unsignedLeftShift_v, moduleShiftFunctor_map_eval]
  simpa only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.id_comp, shiftFunctor_map_f'] using!
      smallStrictBarUnshiftedColumn_naturality A J η s (q + (s.1 : ℤ)) q (by omega)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
