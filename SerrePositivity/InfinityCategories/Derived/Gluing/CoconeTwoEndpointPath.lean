module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexTwoEndpointPath

/-! 同じ差の cocone を、元の二つの鎖写像を始終点とする path 複体へ写す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q : Complex R} (a b : P ⟶ Q)

def dgGluingCoconeTwoEndpointPath : mappingCocone (b - a) ⟶ dgGluingComplexPath Q :=
  biprod.lift (mappingCocone.fst (b - a) ≫ a) (dgGluingCoconePathMap (b - a))

lemma dgGluingCoconeTwoEndpointPath_start :
    dgGluingCoconeTwoEndpointPath a b ≫ dgGluingComplexPathStart Q =
      mappingCocone.fst (b - a) ≫ a := by
  exact biprod.lift_fst _ _

lemma dgGluingCoconeTwoEndpointPath_end :
    dgGluingCoconeTwoEndpointPath a b ≫ dgGluingComplexPathEnd Q =
      mappingCocone.fst (b - a) ≫ b := by
  simp only [dgGluingComplexPathEnd, complexQuasiIsoSpanRight, Category.comp_id,
    Preadditive.comp_add, ← Category.assoc, dgGluingCoconeTwoEndpointPath,
    biprod.lift_fst, biprod.lift_snd, dgGluingCoconePathMap_fst,
    Preadditive.comp_sub]
  abel

lemma dgGluingCoconeTwoEndpointPath_endpoints :
    dgGluingCoconeTwoEndpointPath a b ≫ dgGluingComplexPathEndpoints Q =
      mappingCocone.fst (b - a) ≫ biprod.lift a b := by
  apply biprod.hom_ext
  · simp only [Category.assoc, dgGluingComplexPathEndpoints, biprod.lift_fst]
    exact dgGluingCoconeTwoEndpointPath_start a b
  · simp only [Category.assoc, dgGluingComplexPathEndpoints, biprod.lift_snd]
    exact dgGluingCoconeTwoEndpointPath_end a b

lemma dgGluingCoconeTwoEndpointPath_primitive :
    (Cochain.ofHom (dgGluingCoconeTwoEndpointPath a b)).comp
      (dgGluingComplexPathPrimitive Q) (zero_add (-1)) = mappingCocone.snd (b - a) := by
  apply Cochain.ext
  intro n k hnk
  simp only [dgGluingComplexPathPrimitive, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    dgGluingCoconeTwoEndpointPath]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, biprod.lift_snd]
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    Cochain.congr_v (dgGluingCoconePathMap_snd (b - a)) n k hnk

end SerrePositivity.InfinityCategories
