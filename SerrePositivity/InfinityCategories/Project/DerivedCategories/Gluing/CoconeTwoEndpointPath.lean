module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexTwoEndpointPath

/-! 同じ差の cocone を、元の二つの鎖写像を始終点とする path 複体へ写す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q : Complex R} (a b : P ⟶ Q)

def dgGluingCoconeTwoEndpointPath : mappingCocone (b - a) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q :=
  biprod.lift (mappingCocone.fst (b - a) ≫ a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathMap (b - a))

lemma dgGluingCoconeTwoEndpointPath_start :
    dgGluingCoconeTwoEndpointPath a b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q =
      mappingCocone.fst (b - a) ≫ a := by
  exact biprod.lift_fst _ _

lemma dgGluingCoconeTwoEndpointPath_end :
    dgGluingCoconeTwoEndpointPath a b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q =
      mappingCocone.fst (b - a) ≫ b := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight, Category.comp_id,
    Preadditive.comp_add, ← Category.assoc, dgGluingCoconeTwoEndpointPath,
    biprod.lift_fst, biprod.lift_snd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathMap_fst,
    Preadditive.comp_sub]
  abel

lemma dgGluingCoconeTwoEndpointPath_endpoints :
    dgGluingCoconeTwoEndpointPath a b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q =
      mappingCocone.fst (b - a) ≫ biprod.lift a b := by
  apply biprod.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints, biprod.lift_fst]
    exact dgGluingCoconeTwoEndpointPath_start a b
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints, biprod.lift_snd]
    exact dgGluingCoconeTwoEndpointPath_end a b

lemma dgGluingCoconeTwoEndpointPath_primitive :
    (Cochain.ofHom (dgGluingCoconeTwoEndpointPath a b)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathPrimitive Q) (zero_add (-1)) = mappingCocone.snd (b - a) := by
  apply Cochain.ext
  intro n k hnk
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathPrimitive, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    dgGluingCoconeTwoEndpointPath]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, biprod.lift_snd]
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathMap_snd (b - a)) n k hnk

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
