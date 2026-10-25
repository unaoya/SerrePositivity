module
public import SerrePositivity.DifferentialGraded.Presentation.CategoryReindexInverse
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedTransport
/-!
概要：逆再添字の後の評価を、全 Hom を含む元の恒等 dg 関手と同定する。
方針：保持した等式同型の共役と、その逆の等式移送を相殺する。
規約：閉零射上の自然同型だけに弱めず、dg 関手の等式を証明する。
使われ方：κ-small 共通提示の各成分から元の評価関手を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory KST.SConstruction
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (X : Type u)
  (c : DGCategoryPresentationData R κ.ord.ToType X) (a : κ.ord.ToType) (e : Set.Iio a ≃ X)
namespace DGCategoryPresentationData

lemma reindexInverse_comp_evaluation :
    letI := c.enrichment R κ.ord.ToType X
    (reindexInverse R κ X c a e).comp (reindexEvaluation R κ X c a e) =
      DGFunctor.id X := by
  letI := c.enrichment R κ.ord.ToType X
  apply EnrichedFunctor.ext (Complex R) (fun x => e.apply_symm_apply x)
  intro x y
  rw [inducedDGHom_eqToHom R (id : X → X)
    (e.apply_symm_apply x) (e.apply_symm_apply y)]
  change ((𝟙 _ ≫ 𝟙 _) ≫ enrichedClosedIsoConjugation (Complex R)
    (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply x).symm))
    (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply y).symm))) ≫
      𝟙 _ ≫ enrichedClosedIsoConjugation (Complex R)
        (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply x)))
        (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply y))) = 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rw [enrichedClosedIsoConjugation_trans]
  simp [enrichedClosedIsoConjugation]

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
