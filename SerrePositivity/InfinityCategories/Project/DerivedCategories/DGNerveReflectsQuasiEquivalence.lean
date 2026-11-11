module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGResolutionHomologyDetection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedGradedShift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-! # 前三角な始域に対する dg nerve の準同値の反映

通常の h と H⁰ の自然な比較で nerve の同値を H⁰ へ移す。
始域の斉次 shift 証人により全 Hom 次数を検出する。標的の前三角性は不要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

/-- dg nerve が同値なら、同じ dg 関手の H⁰ 作用は圏同値である。 -/
lemma dgFunctor_onHomotopy_isEquivalence_of_nerve (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)) :
    F.onHomotopy.IsEquivalence := by
  let HC := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C
  let HE := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R E
  let : (SSet.hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)).toFunctor.IsEquivalence :=
    hF.choose.toHoEquivalence.isEquivalence_functor
  let : ((SSet.hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)).toFunctor ⋙ HE.functor).IsEquivalence :=
    inferInstance
  let : (HC.functor ⋙ F.onHomotopy).IsEquivalence :=
    Functor.isEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_naturalityIso R C E F)
  exact Functor.isEquivalence_of_comp_left HC.functor F.onHomotopy

variable [Small.{u} C] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C]

/-- 前三角な始域では、native dg nerve の同値は全 Hom の準同型性を反映する。 -/
theorem dgFunctor_homQuasiIso_of_nerve (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)) : HomQuasiIso F := by
  let := dgFunctor_onHomotopy_isEquivalence_of_nerve R C E F hF
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_homQuasiIso_of_gradedShifts R C E F
  intro x n
  obtain ⟨w, f, g, hf, hg, h, hh⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulated_gradedShiftWitness R C x (-n)
  let f' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) rfl rfl (neg_neg n) f
  have hf' : _root_.SerrePositivity.DifferentialGraded.differential R f' = 0 := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential, hf, map_zero]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose (A := R) rfl rfl rfl
    (neg_neg n) rfl rfl g f (neg_add_cancel (-n))
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact ⟨w, f', g, hf', hg, h, hh.trans (congrArg (· - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val) hc)⟩

/-- 始域だけが前三角な dg 関手について、native dg nerve の同値は準同値を反映する。 -/
theorem dgFunctor_quasiEquivalence_of_nerve (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)) : QuasiEquivalence F := by
  let := dgFunctor_onHomotopy_isEquivalence_of_nerve R C E F hF
  exact ⟨dgFunctor_homQuasiIso_of_nerve R C E F hF, inferInstance⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
