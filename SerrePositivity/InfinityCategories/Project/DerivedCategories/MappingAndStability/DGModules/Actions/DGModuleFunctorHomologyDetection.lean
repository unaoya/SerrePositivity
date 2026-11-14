module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorHomologyDetection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleDerivedFunctor
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGQuasiEquivalenceNerve
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
/-!
概要：射影的加群上の H⁰ の充満忠実性から、全 Hom 鎖写像の準同型性を回収する。
方針：全 source shift の H⁰ を、同じ dg 関手の正規化 shift 同型で Hⁿ へ同定する。
規約：H⁰ の同値だけを根拠に ∞ 圏同値としない。使われ方：β5 の Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory HomologicalComplex DifferentialGraded MonoidalCategory SSet
variable (R : Type u) [CommRing R] (D E : Type v)
variable [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の Hom 鎖写像の H^(-s) は、源を s シフトした同じ Hom 鎖写像の H⁰。 -/
lemma dgModuleFunctor_hom_quasiIsoAt_shift_iff
    (F : DGFunctor R (RightModule R D) (RightModule R E)) (M N : RightModule R D) (s : ℤ) :
    QuasiIsoAt (F.map (shiftModule s M) N) 0 ↔ QuasiIsoAt (F.map M N) (-s) := by
  let e := normalizedDGModuleFunctorShiftIso R D E F s M
  let p := eHomWhiskerRight (Complex R) e.inv (ForgetEnrichment.of (Complex R) (F.obj N))
  let ep := ((eHomFunctor (Complex R) (ModuleCategory R E)).mapIso e.op).app
    (ForgetEnrichment.of (Complex R) (F.obj N))
  have hp : p = ep.inv := rfl
  have : IsIso p := by rw [hp]; infer_instance
  let a := F.map M N
  let b := F.map (shiftModule s M) N
  let eT := moduleHomSourceShiftIso R E (F.obj M) (F.obj N) s
  let eS := moduleHomSourceShiftIso R D M N s
  calc
    QuasiIsoAt b 0 ↔ QuasiIsoAt (b ≫ p) 0 := (quasiIsoAt_iff_comp_right b p 0).symm
    _ ↔ QuasiIsoAt ((b ≫ p) ≫ eT.hom) 0 :=
      (quasiIsoAt_iff_comp_right _ eT.hom 0).symm
    _ ↔ QuasiIsoAt (eS.hom ≫ (CategoryTheory.shiftFunctor (Complex R) (-s)).map a) 0 := by
      rw [Category.assoc, Morita.criterionPerfDGFunctorHom_sourceShift]
    _ ↔ QuasiIsoAt ((CategoryTheory.shiftFunctor (Complex R) (-s)).map a) 0 :=
      quasiIsoAt_iff_comp_left eS.hom _ 0
    _ ↔ QuasiIsoAt a (-s) := CochainComplex.quasiIsoAt_shift_iff a (-s) 0 (-s) (by omega)
/-- 射影的部分圏上の H⁰ の充満忠実性は、同じ実 dg 関手の全 Hom 準同型性を与える。 -/
theorem dgProjectiveModuleFunctor_homQuasiIso_of_ho
    (F : DGFunctor R (RightModule R D) (RightModule R E))
    (hF : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (F.obj M))
    [(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF).onHomotopy.Full]
    [(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF).onHomotopy.Faithful] :
    HomQuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF) := by
  intro M N
  rw [quasiIso_iff]
  intro j
  change QuasiIsoAt (F.map M.val N.val) j
  let S : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D := ⟨shiftModule (-j) M.val,
    moduleHomotopicallyProjective_shift R D M.property (-j)⟩
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_quasiIsoAt_zero_of_ho_map_bijective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF)
    (ForgetEnrichment.of (Complex R) S) (ForgetEnrichment.of (Complex R) N)
    ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF).onHomotopy.map_injective,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF).onHomotopy.map_surjective⟩
  simpa only [neg_neg] using
    (dgModuleFunctor_hom_quasiIsoAt_shift_iff R D E F M.val N.val (-j)).mp hz
/-- H⁰ の射影的模型上で同値となる dg 関手は、半自由模型の実導来 ∞ 関手でも同値。 -/
theorem dgModuleDerivedFunctor_isQCatEquivalence_of_ho
    (F : DGFunctor R (RightModule R D) (RightModule R E))
    (hF : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (F.obj M))
    [(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF).onHomotopy.IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor R D E F hF) := by
  have hq := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF)
    ⟨dgProjectiveModuleFunctor_homQuasiIso_of_ho R D E F hF, inferInstance⟩
  have hi := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.symm.isQCatEquivalence
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.inv at hi
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).comp (hq.comp hi)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
