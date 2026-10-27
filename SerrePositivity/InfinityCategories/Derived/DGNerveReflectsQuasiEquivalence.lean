module
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyNaturality
public import SerrePositivity.InfinityCategories.Derived.DGResolutionHomologyDetection
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedGradedShift
public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-! # 前三角な始域に対する dg nerve の準同値の反映

通常の h と H⁰ の自然な比較で nerve の同値を H⁰ へ移す。
始域の斉次 shift 証人により全 Hom 次数を検出する。標的の前三角性は不要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C E : Type v) [DGCategory R C] [DGCategory R E]

/-- dg nerve が同値なら、同じ dg 関手の H⁰ 作用は圏同値である。 -/
lemma dgFunctor_onHomotopy_isEquivalence_of_nerve (F : DGFunctor R C E)
    (hF : IsQCatEquivalence (dgNerve.map F)) :
    F.onHomotopy.IsEquivalence := by
  let HC := dgStableHomotopyEquivalence R C
  let HE := dgStableHomotopyEquivalence R E
  let : (SSet.hoFunctor.map (dgNerve.map F)).toFunctor.IsEquivalence :=
    hF.choose.toHoEquivalence.isEquivalence_functor
  let : ((SSet.hoFunctor.map (dgNerve.map F)).toFunctor ⋙ HE.functor).IsEquivalence :=
    inferInstance
  let : (HC.functor ⋙ F.onHomotopy).IsEquivalence :=
    Functor.isEquivalence_of_iso (dgStableHomotopyEquivalence_naturalityIso R C E F)
  exact Functor.isEquivalence_of_comp_left HC.functor F.onHomotopy

variable [Small.{u} C] [IsDGPretriangulated R C]

/-- 前三角な始域では、native dg nerve の同値は全 Hom の準同型性を反映する。 -/
theorem dgFunctor_homQuasiIso_of_nerve (F : DGFunctor R C E)
    (hF : IsQCatEquivalence (dgNerve.map F)) : HomQuasiIso F := by
  let := dgFunctor_onHomotopy_isEquivalence_of_nerve R C E F hF
  apply dgFunctor_homQuasiIso_of_gradedShifts R C E F
  intro x n
  obtain ⟨w, f, g, hf, hg, h, hh⟩ := dgPretriangulated_gradedShiftWitness R C x (-n)
  let f' := gradedHomTransport (A := R) rfl rfl (neg_neg n) f
  have hf' : differential R f' = 0 := by
    rw [← gradedHomTransport_differential, hf, map_zero]
  have hc := gradedHomTransport_compose (A := R) rfl rfl rfl
    (neg_neg n) rfl rfl g f (neg_add_cancel (-n))
  simp only [gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact ⟨w, f', g, hf', hg, h, hh.trans (congrArg (· - (unitElement R x).val) hc)⟩

/-- 始域だけが前三角な dg 関手について、native dg nerve の同値は準同値を反映する。 -/
theorem dgFunctor_quasiEquivalence_of_nerve (F : DGFunctor R C E)
    (hF : IsQCatEquivalence (dgNerve.map F)) : QuasiEquivalence F := by
  let := dgFunctor_onHomotopy_isEquivalence_of_nerve R C E F hF
  exact ⟨dgFunctor_homQuasiIso_of_nerve R C E F hF, inferInstance⟩

end SerrePositivity.InfinityCategories
