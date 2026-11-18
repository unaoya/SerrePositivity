module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneFibration
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneQuasiIso
public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-!
# Γ の cone の射影は Kan fibration

DAG XIII §2.2 の Ω 比較への前段。元の cone の指定第三射と次数付き section を使う。
恒等射の cone についても、実際の零射が全基点 π 同型になることを示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 元の cone の第三射は、既存の次数付き section により実射影 fibration。 -/
lemma coneProjection_projectiveFibration {M N : Complex A} (f : M ⟶ N) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (mappingCone.triangle f).mor₃ := by
  intro n y
  refine ⟨complexConeGradedSection f n y, ?_⟩
  rw [complexConeGradedProjection_eq_connecting]
  exact ConcreteCategory.congr_hom (complexConeGradedSection_connecting f n) y

open SSet.modelCategoryQuillen in
/-- 同じ cone の第三射の Γ は、零次数の境界も含む Kan fibration。 -/
lemma gammaConeProjection_fibration {M N : Complex A} (f : M ⟶ N) :
    HomotopicalAlgebra.Fibration
      ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (mappingCone.triangle f).mor₃) :=
  gammaMap_fibration A _ (coneProjection_projectiveFibration A f)

/-- 恒等射の元の cone は非輪状。 -/
lemma identityCone_acyclic (M : Complex A) : (mappingCone (𝟙 M)).Acyclic :=
  (SerrePositivity.cochain_quasiIso_iff_cone_acyclic (𝟙 M)).mp inferInstance

/-- 恒等射の cone から零複体への同じ零射は準同型。 -/
lemma identityCone_zero_quasiIso (M : Complex A) :
    QuasiIso (0 : mappingCone (𝟙 M) ⟶ (HomologicalComplex.zero : Complex A)) := by
  have hz : (HomologicalComplex.zero : Complex A).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ HomologicalComplex.isZero_zero
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact ((identityCone_acyclic A M i).isZero_homology).isIso
    ((hz i).isZero_homology) _

/-- 同じ零射の Γ は、全基点・全次数の π 同型である。 -/
lemma gammaIdentityCone_zero_piIsomorphism (M : Complex A) :
    SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map
        (0 : mappingCone (𝟙 M) ⟶ (HomologicalComplex.zero : Complex A))) := by
  have := identityCone_zero_quasiIso A M
  exact gammaMap_kanPiIsomorphism _

end SerrePositivity.EInfinity.PowerOperation
