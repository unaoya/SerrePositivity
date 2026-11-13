module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomConeTargetComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.KernelHomComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.YonedaPostActionInverse

/-! 係数円錐の左包含を、同じ通常 tensor 像の左包含の全 Hom 作用へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)) f
local notation "yf" => CategoryTheory.Functor.map (DGFunctor.onClosed (dgYoneda R D)) rf
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R D yf)

/-- 係数標的同型は、左包含を同じ tensor 左包含の全次数作用へ送る。 -/
lemma dgGluingHomConeRightTensorTargetIso_inl :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso R C D M X Y Z f).hom)
      (add_zero (-1)) =
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomTargetIso R C D M X Y).hom).comp
      ((modulePostcompositionMap R C (representable R X.left)
        ((F).obj (representable R Y.right)) ((F).obj K)).f (-1)
        (dgModuleFunctorConeInl R D C F yf)) (zero_add (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeIso_inl_eval R C D M rf X.left]
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaPostAction_inv R C ((F).obj (representable R Y.right))
    ((F).obj K) (-1) X.left (dgModuleFunctorConeInl R D C F yf)
  change (DGFunctor.moduleConeImageInl R D ((F).comp (moduleEvaluationDG R C X.left)) yf).comp
    (Cochain.ofHom (dgYonedaIso R X.left ((F).obj K)).inv) (add_zero (-1)) = _ at he
  rw [he, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
