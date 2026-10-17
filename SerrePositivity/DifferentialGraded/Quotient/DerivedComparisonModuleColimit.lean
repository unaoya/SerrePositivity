module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLengthModule
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationColimit
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects

/-! # 制限代表加群を長さ部分加群の逐次余極限として復元する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 加群の長さ図式を評価すると Hom の長さ図式になる。 -/
def lengthModuleDiagramEvaluationIso (S : Set D) (z x : D) :
    lengthModuleDiagram A D S z ⋙ moduleEvaluation A D x ≅ lengthDiagram A D S x z :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro m n f
    change (moduleEvaluation A D x).map (lengthModuleTransition A D S z (leOfHom f)) ≫
      𝟙 _ = 𝟙 _ ≫ lengthMap A D S x z (leOfHom f)
    rw [Category.comp_id, Category.id_comp, lengthModuleTransition_eval])

def lengthModuleCoconeEvaluationIso (S : Set D) (z x : D) :
    (Cocone.precompose (lengthModuleDiagramEvaluationIso A D S z x).hom).obj
        (lengthCocone A D S x z) ≅
      (moduleEvaluation A D x).mapCocone (lengthModuleCocone A D S z) :=
  Cocone.ext (Iso.refl _) (by
    intro n
    change (𝟙 _ ≫ lengthInclusion A D S x z n) ≫ 𝟙 _ =
      (moduleEvaluation A D x).map (lengthModuleInclusion A D S z n)
    rw [Category.id_comp, Category.comp_id, lengthModuleInclusion_eval])

def lengthModuleCocone_eval_isColimit (S : Set D) (z x : D) :
    IsColimit ((moduleEvaluation A D x).mapCocone (lengthModuleCocone A D S z)) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (lengthModuleDiagramEvaluationIso A D S z x)
      (lengthCocone A D S x z)).symm (lengthCocone_isColimit A D S x z))
    (lengthModuleCoconeEvaluationIso A D S z x)

/-- 商の制限代表加群は、全長さ部分加群の加群圏内での余極限である。 -/
def lengthModuleCocone_isColimit (S : Set D) (z : D) :
    IsColimit (lengthModuleCocone A D S z) :=
  moduleIsColimitOfEvaluations A D _ (lengthModuleCocone_eval_isColimit A D S z)

instance lengthModuleDiagram_hasColimit (S : Set D) (z : D) :
    HasColimit (lengthModuleDiagram A D S z) :=
  HasColimit.mk ⟨_, lengthModuleCocone_isColimit A D S z⟩

def lengthModuleColimitIso (S : Set D) (z : D) :
    colimit (lengthModuleDiagram A D S z) ≅
      ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (lengthModuleCocone_isColimit A D S z)

@[reassoc] lemma lengthModuleColimitIso_ι (S : Set D) (z : D) (n : ℕ) :
    colimit.ι (lengthModuleDiagram A D S z) n ≫ (lengthModuleColimitIso A D S z).hom =
      lengthModuleInclusion A D S z n :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ n

end SerrePositivity.DifferentialGraded.DGQuotient
