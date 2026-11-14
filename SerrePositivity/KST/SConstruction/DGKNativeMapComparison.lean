module
public import SerrePositivity.KST.SConstruction.DGKNativeValueComparison
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionComposition
public import SerrePositivity.KST.SConstruction.DGStandardClosedComparisonIso
public import SerrePositivity.KST.SConstruction.DGStandardFunctorIsoReflection
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEvaluationNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGUniverseLiftFunctor

/-!
概要：同じ入力宇宙下降と dg 関手による実 Perf 延長の四角形を比較する。
方針：元の全 Hom 自然な合成同型を native 関手同型へ反映する。
規約：元の厳密 dg 関手と一回延長を保持する。
使われ方：d④ の native 二辺と固定 ν 二辺の全自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (D E T : Type (u + 1))
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R T] [Small.{u} T]

/-- 概要：元の実 Perf 延長の合成は一回延長と native 関手同型を持つ。
方針：元の全 Hom 閉零比較を同じ native nerve へ反映する。
規約：比較の全自然性を保持する。使われ方：宇宙下降との比較四角形。 -/
def dgKPerfectNativeCompositionIso (F : DGFunctor R D E) (G : DGFunctor R E T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R E T G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D T (F.comp G))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  exact dgStandardFunctorIso_to_native (dgStandardClosedComparisonIso _ _
    (perfectDGExtensionCompositionAt R D E T F G)
    (perfectDGExtensionCompositionAt_naturality R D E T F G))

omit [DGCategory R T] [Small.{u} T] in
/-- 概要：同じ入力持ち上げの Perf 延長後の下降は、下降後の元延長と比較できる。
方針：実合成同型と元の strict 下降四角形を使用する。
規約：二つの二回延長を保持する。使われ方：固定 ν の実辺の評価後の回収。 -/
def dgKNativePerfectDownMapComparison (F : DGFunctor R D E) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} F)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R E)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R D)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F)) := by
  let a := dgKPerfectNativeCompositionIso R _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R E)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp_down] at a
  exact a.trans (dgKPerfectNativeCompositionIso R _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R D) F).symm


omit [DGCategory R T] [Small.{u} T] in
/-- 概要：元の厳密 dg 関手を同じ固定 S の辺にする。
方針：元の全 Hom を保つ対象宇宙の持ち上げ。
規約：入力関手を選び直さない。使われ方：native 二辺の固定 ν 像。 -/
def dgKNativeInputMap (F : DGFunctor R D E) :
    dgKUniverseInput.{u, u + 1, u + 1} R D ⟶
      dgKUniverseInput.{u, u + 1, u + 1} R E :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} F)

omit [DGCategory R T] [Small.{u} T] in
/-- 概要：同じ固定 S 辺の元の ν 完全射。
方針：固定界面をそのまま適用する。規約：型付きの元の安定値を保持する。
使われ方：native 比較の自然性四角形の右辺。 -/
abbrev dgKNativeInputExactMap (F : DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R (dgKUniverseInput.{u, u + 1, u + 1} R D))
      (dgKInputStableValue R (dgKUniverseInput.{u, u + 1, u + 1} R E)) :=
  dgKInputNuMap R (dgKNativeInputMap R D E F)

omit [DGCategory R T] [Small.{u} T] in
/-- 概要：同じ固定 ν 辺を評価すると元 dg 関手の一回 Perf 延長を回収する。
方針：元の評価自然性と同じ宇宙下降比較を合成する。
規約：対象別同型ではなく全関手同型。使われ方：native 二辺との照合。 -/
def dgKNativeInputMapEvaluationComparison [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D]
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R E] (F : DGFunctor R D E) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKNativeInputExactMap R D E F).hom ≫ (dgKNativePerfectValueEquivalence R E).inv)
    ((dgKNativePerfectValueEquivalence R D).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F)) := by
  have a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp ((presentedPerfectDGEvaluationNativeComparison R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} F)).symm)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R E)))
  have b := (dgKNativePerfectDownMapComparison R D E F).precomp
    (presentedPerfectDGQCatEvaluationEquivalence R
      (dgKUniverseInput.{u, u + 1, u + 1} R D)).hom
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} D)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} F)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R E))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} D)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R D)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F))) at b
  unfold dgKNativeInputExactMap
  rw [dgKInputNuMap_eq]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} F)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} E)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R E))))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} D)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} D) D
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R D))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using a.trans b

end SerrePositivity.KST.SConstruction
