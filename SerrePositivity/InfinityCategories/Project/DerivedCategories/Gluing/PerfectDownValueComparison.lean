module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PerfectNativeCompositionIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.EquivalenceSquareInverse
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEvaluationNaturality
/-!
概要：実宇宙下降と指定 Perf 評価の逆で、元の延長を入力作用へ照合する。
方針：下降の全自然性と評価の全自然性を、指定往復同型で逆向きに運ぶ。
規約：入力の同値とその逆を保持する。使われ方：元二脚の固定入力への全比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [Small.{u} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} D)]
  [Small.{u} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} E)]

def perfectDownValueComparison (F : DGFunctor R D E)
    (dD : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} D)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R D)))
    (dE : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} E)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R E)))
    (eD : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} D)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} D))))
    (eE : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} E)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} E))))
    (hdD : dD.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R D)))
    (hdE : dE.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R E)))
    (heD : eD.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} D)))
    (heE : eE.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} E))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F) ≫ (dE.symm.trans eE.symm).hom)
      ((dD.symm.trans eD.symm).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, v, u + 1, u + 1} F))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.equivalenceSquareTwoInverse dD dE eD eE
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, v, u + 1, u + 1} F)))
  · rw [hdD, hdE]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.perfectNativeDownMapComparison R D E F
  · rw [heD, heE]
    exact presentedPerfectDGEvaluationNativeComparison R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, v, u + 1, u + 1} F)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
