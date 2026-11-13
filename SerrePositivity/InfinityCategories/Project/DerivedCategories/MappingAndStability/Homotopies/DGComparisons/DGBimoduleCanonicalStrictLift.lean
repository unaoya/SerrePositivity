module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionStrictLift
public import SerrePositivity.DifferentialGraded.Bimodule.Right
/-!
概要：双加群の指定 canonical 半自由分解間に、厳密な augmentation square を持つ射を作る。
方針：積 dg 圏上の実 strict lift を元の圏同値で戻し、指定余単位の自然性を使う。
規約：既存の導来可換な lift を置き換えない。使われ方：canonical cell 模型の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (B C : Type v)
  [DGCategory R B] [Small.{u} B] [DGCategory R C] [Small.{u} C]
local notation "J" => rightModuleBimoduleEquivalence R B C
local notation "K" => (DGTensorCategory R Bᵒᵖ C)ᵒᵖ
def dgBimoduleCanonicalResolutionStrictLift {P Q : BimoduleCategory R B C} (f : P ⟶ Q) :
    (bimoduleCanonicalSemifreeResolution R B C P).obj ⟶
      (bimoduleCanonicalSemifreeResolution R B C Q).obj :=
  (J).functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionStrictLift R K ((J).inverse.obj P) ((J).inverse.map f)
    (moduleResolutionCandidateπ R K ((J).inverse.obj Q))
    (moduleResolutionCandidateπ_degreewiseSurjective R K ((J).inverse.obj Q))
    (moduleResolutionCandidateπ_quasiIso R K ((J).inverse.obj Q)))
lemma dgBimoduleCanonicalResolutionStrictLift_fac {P Q : BimoduleCategory R B C} (f : P ⟶ Q) :
    dgBimoduleCanonicalResolutionStrictLift R B C f ≫
        (bimoduleCanonicalSemifreeResolution R B C Q).π =
      (bimoduleCanonicalSemifreeResolution R B C P).π ≫ f := by
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionStrictLift R K ((J).inverse.obj P) ((J).inverse.map f)
    (moduleResolutionCandidateπ R K ((J).inverse.obj Q))
    (moduleResolutionCandidateπ_degreewiseSurjective R K ((J).inverse.obj Q))
    (moduleResolutionCandidateπ_quasiIso R K ((J).inverse.obj Q))
  have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionStrictLift_fac R K ((J).inverse.obj P) ((J).inverse.map f)
    (moduleResolutionCandidateπ R K ((J).inverse.obj Q))
    (moduleResolutionCandidateπ_degreewiseSurjective R K ((J).inverse.obj Q))
    (moduleResolutionCandidateπ_quasiIso R K ((J).inverse.obj Q))
  have ht := congrArg (fun c => (J).functor.map c) hb
  simp only [CategoryTheory.Functor.map_comp] at ht
  change (J).functor.map b ≫
      ((J).functor.map (moduleResolutionCandidateπ R K ((J).inverse.obj Q)) ≫
        ((J).counitIso.app Q).hom) =
    ((J).functor.map (moduleResolutionCandidateπ R K ((J).inverse.obj P)) ≫
      ((J).counitIso.app P).hom) ≫ f
  calc
    _ = ((J).functor.map b ≫
        (J).functor.map (moduleResolutionCandidateπ R K ((J).inverse.obj Q))) ≫
          ((J).counitIso.app Q).hom := (Category.assoc _ _ _).symm
    _ = ((J).functor.map (moduleResolutionCandidateπ R K ((J).inverse.obj P)) ≫
        (J).functor.map ((J).inverse.map f)) ≫ ((J).counitIso.app Q).hom :=
      congrArg (fun c => c ≫ ((J).counitIso.app Q).hom) ht
    _ = _ := by
      simpa only [Category.assoc] using!
        congrArg (fun c =>
          (J).functor.map (moduleResolutionCandidateπ R K ((J).inverse.obj P)) ≫ c)
          ((J).counitIso.hom.naturality f)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
