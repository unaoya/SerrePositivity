module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGResolutionHomologyDetection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelResolutionHomotopyMorita
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice
/-!
概要：一般双加群の主導来 Morita 同値を、元の実半自由 ∞ 関手の同値へ昇格する。
方針：実分解圏の H⁰ 同値、斉次 shift による全 Hom 検査、実入力切断を合成する。
規約：出力の射影性や局所 Hom の平坦性は追加しない。使われ方：β5 e の D の結論。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ一般 kernel の主導来同値を実半自由模型へ移す。 -/
lemma dgKernelResolutionReplacement_homQuasiIso
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    HomQuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionReplacement_onHomotopy_isEquivalence R D E P
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolution_homQuasiIso_of_ho R D E _ _ _
/-- 同じ一般 kernel の主導来同値を実半自由模型へ移す。 -/
lemma dgKernelResolutionReplacement_quasiEquivalence
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    QuasiEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionReplacement_onHomotopy_isEquivalence R D E P
  exact ⟨dgKernelResolutionReplacement_homQuasiIso R D E P, inferInstance⟩
/-- 同じ一般 kernel の主導来同値を実半自由模型へ移す。 -/
lemma dgKernelDerivedInfinity_isQCatEquivalence_of_classical
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence G
      (dgKernelResolutionReplacement_quasiEquivalence R D E P)
  let U := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
  let V := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
  let i : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)) :=
    { hom := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map U
      inv := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map V
      hom_inv_id := by
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]
      inv_hom_id := by
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown_comp_up, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id] }
  have hS := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F).symm.isQCatEquivalence
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso i).isQCatEquivalence.comp (hS.comp hG)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map U ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) at h
  have hE := congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down.{u, max (u + 1) v, max (u + 1) v} R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id] at hE
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc,
    hE, Category.comp_id, U, F, G] using h
/-- 同じ一般 kernel の主導来同値を実半自由模型へ移す。 -/
lemma dgKernelDerivedInfinity_isExactFunctor_of_classical
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (dgKernelDerivedInfinity_isQCatEquivalence_of_classical R D E P)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
