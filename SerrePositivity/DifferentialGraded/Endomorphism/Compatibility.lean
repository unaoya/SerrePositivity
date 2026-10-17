module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedEvaluation
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHom
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftConeComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.GeneratorHomIso
public import SerrePositivity.DifferentialGraded.Endomorphism.HomComparisonShift
public import SerrePositivity.DifferentialGraded.Endomorphism.ThickHomComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.QuasiFullyFaithful
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectImage
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectDGComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHomHomotopyComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectEquivalence
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementShiftTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementTensorTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectScalarTensor
public import SerrePositivity.DifferentialGraded.Endomorphism.CompactUnitCounit
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedEquivalenceTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarEvaluationActual
public import SerrePositivity.DifferentialGraded.Endomorphism.ActualScalarEnd
public import SerrePositivity.DifferentialGraded.Endomorphism.ActualScalarEvaluation
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarYonedaHom
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarYonedaIso
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarClosedMap
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomRetracts
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomHomotopyRetracts
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectHom
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarEnhancementDerivedComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensorEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementShiftComparison

/-! # 指定対象のEndとshift・underived係数変更の正方形

非flat係数変更でもunderived Endの正方形は構成できる。
導来係数変更との一致や全Homの係数変更の同型性は主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (E : D)

/-- Endを取って係数変更した一対象dg圏から、係数変更した指定対象のEndへの比較。 -/
def endomorphismScalarComparison :
    DGFunctor A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (EndomorphismObject (show ScalarExtension.DGBaseChange φ D from E)) where
  obj _ := .point
  map _ _ := 𝟙 _
  map_id _ := by simp only [Category.comp_id]; rfl
  map_comp _ _ _ := by
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl

/-- 係数変更後のEndの包含は、元の包含の係数変更と可換。 -/
lemma endomorphismScalarComparison_square :
    (endomorphismScalarComparison φ D E).comp
      (endomorphismInclusion A' (show ScalarExtension.DGBaseChange φ D from E)) =
    ScalarExtension.dgFunctor φ (endomorphismInclusion A E) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (endomorphismScalarComparison φ D E).comp
      (endomorphismInclusion A' (show ScalarExtension.DGBaseChange φ D from E)))
    (G := ScalarExtension.dgFunctor φ (endomorphismInclusion A E)) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, endomorphismScalarComparison,
    endomorphismInclusion, ScalarExtension.dgFunctor, Category.comp_id,
    CategoryTheory.Functor.map_id, eqToHom_refl]
  rfl

variable (A) [Small.{u} D]

/-- U13の実際のdg shiftに沿う、指定対象のEndと包含の可換正方形。 -/
lemma perfectEndomorphismShift_square (S : Set D) (E : PerfectDGModuleOver A D S) (s : ℤ) :
    (endomorphismMap A (perfectDGModuleShiftDG A D S s) E).comp
        (endomorphismInclusion A ((perfectDGModuleShiftDG A D S s).obj E)) =
      (endomorphismInclusion A E).comp (perfectDGModuleShiftDG A D S s) :=
  endomorphismMap_comp_inclusion A (perfectDGModuleShiftDG A D S s) E

end SerrePositivity.DifferentialGraded
