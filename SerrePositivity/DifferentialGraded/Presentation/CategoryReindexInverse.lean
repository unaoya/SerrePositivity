module
public import SerrePositivity.DifferentialGraded.Presentation.CategoryReindex
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedConjugate
/-!
概要：提示の対象再添字を逆向きの全 Hom dg 関手として実現する。
方針：同値の逆写像を対象作用に保ち、評価後の等式同型で全次数を共役する。
規約：既存の一般共役入口を再利用し、提示の Hom データを選び直さない。
使われ方：非連結和の各成分を ordinal コードへ戻した共通提示へ包含する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (X : Type u)
  (c : DGCategoryPresentationData R κ.ord.ToType X) (a : κ.ord.ToType) (e : Set.Iio a ≃ X)
namespace DGCategoryPresentationData

def reindexInverse :
    letI := c.enrichment R κ.ord.ToType X
    DGFunctor R X ((reindex R κ X c a e).Objects R κ) := by
  letI := c.enrichment R κ.ord.ToType X
  exact inducedDGFunctorClosedConjugate R (id : X → X) (e : Set.Iio a → X)
    (DGFunctor.id X) e.symm (fun x =>
      eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply x).symm))

lemma reindexInverse_obj (x : X) :
    letI := c.enrichment R κ.ord.ToType X
    (reindexInverse R κ X c a e).obj x = e.symm x := rfl

/-- 逆再添字の後の実評価は、元の全閉射関手と自然同型になる。 -/
def reindexInverseEvaluationIso :
    letI := c.enrichment R κ.ord.ToType X
    (DGFunctor.id X).onClosed ≅
      ((reindexInverse R κ X c a e).comp (reindexEvaluation R κ X c a e)).onClosed := by
  letI := c.enrichment R κ.ord.ToType X
  exact inducedDGFunctorClosedConjugateIso R (id : X → X) (e : Set.Iio a → X)
    (DGFunctor.id X) e.symm (fun x =>
      eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply x).symm))

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
