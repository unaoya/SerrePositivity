module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PerfectNativeCompositionIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.EquivalenceSquareInverse
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEvaluationNaturality
/-!
概要：実宇宙下降と指定 Perf 評価の逆で、元の延長を入力作用へ照合する。
方針：下降の全自然性と評価の全自然性を、指定往復同型で逆向きに運ぶ。
規約：入力の同値とその逆を保持する。使われ方：元二脚の固定入力への全比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Derived.Gluing
open CategoryTheory SSet DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [Small.{u} (DGUniverseLift.{v, u + 1} D)]
  [Small.{u} (DGUniverseLift.{v, u + 1} E)]

def perfectDownValueComparison (F : DGFunctor R D E)
    (dD : QCatEquivalence (dgNerve R (PerfectDGModule R (DGUniverseLift.{v, u + 1} D)))
      (dgNerve R (PerfectDGModule R D)))
    (dE : QCatEquivalence (dgNerve R (PerfectDGModule R (DGUniverseLift.{v, u + 1} E)))
      (dgNerve R (PerfectDGModule R E)))
    (eD : QCatEquivalence (dgNerve R (PresentedPerfectDGObject R (DGUniverseLift.{v, u + 1} D)))
      (dgNerve R (PerfectDGModule R (DGUniverseLift.{v, u + 1} D))))
    (eE : QCatEquivalence (dgNerve R (PresentedPerfectDGObject R (DGUniverseLift.{v, u + 1} E)))
      (dgNerve R (PerfectDGModule R (DGUniverseLift.{v, u + 1} E))))
    (hdD : dD.hom = dgNerve.map (perfectDGExtension R _ _ (dgUniverseLiftDown R D)))
    (hdE : dE.hom = dgNerve.map (perfectDGExtension R _ _ (dgUniverseLiftDown R E)))
    (heD : eD.hom = dgNerve.map (presentedPerfectDGEvaluation R (DGUniverseLift.{v, u + 1} D)))
    (heE : eE.hom = dgNerve.map (presentedPerfectDGEvaluation R (DGUniverseLift.{v, u + 1} E))) :
    FunctorIso
      (dgNerve.map (perfectDGExtension R D E F) ≫ (dE.symm.trans eE.symm).hom)
      ((dD.symm.trans eD.symm).hom ≫ dgNerve.map (presentedPerfectDGAction R (DGUniverseLift.{v, u + 1} D) (DGUniverseLift.{v, u + 1} E)
        (dgUniverseLiftFunctor.{u, v, v, u + 1, u + 1} F))) := by
  apply equivalenceSquareTwoInverse dD dE eD eE
    (dgNerve.map (perfectDGExtension R (DGUniverseLift.{v, u + 1} D) (DGUniverseLift.{v, u + 1} E)
      (dgUniverseLiftFunctor.{u, v, v, u + 1, u + 1} F)))
  · rw [hdD, hdE]
    exact perfectNativeDownMapComparison R D E F
  · rw [heD, heE]
    exact presentedPerfectDGEvaluationNativeComparison R (DGUniverseLift.{v, u + 1} D) (DGUniverseLift.{v, u + 1} E)
      (dgUniverseLiftFunctor.{u, v, v, u + 1, u + 1} F)

end SerrePositivity.InfinityCategories.Derived.Gluing
