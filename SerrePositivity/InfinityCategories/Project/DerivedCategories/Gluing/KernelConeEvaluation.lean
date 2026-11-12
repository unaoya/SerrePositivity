module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelCone

/-! 双加群の像の円錐から通常 tensor 像への比較は、次数 −1 の包含も保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  {d d' : ClosedCategory R D} (f : d ⟶ d') (c : C)
local notation "mf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed M.toFunctor) f
local notation "yf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgYoneda R D)) f
local notation "F" => Morita.kernelTensor R D C M

/-- 評価した円錐比較の左包含は、列同型の逆と実 tensor の次数 −1 の包含の合成。 -/
lemma dgGluingKernelConeIso_inl_eval :
    (mappingCone.inl ((moduleEvaluation R C c).map mf)).comp
      (Cochain.ofHom ((moduleEvaluation R C c).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeIso R C D M f).hom))
      (add_zero (-1)) =
    (Cochain.ofHom ((moduleEvaluation R C c).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M d).inv)).comp
      (DGFunctor.moduleConeImageInl R D ((F).comp (moduleEvaluationDG R C c)) yf)
      (zero_add (-1)) := by
  apply Cochain.ext
  intro q n hn
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeIso, Iso.trans_hom, Iso.symm_hom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeSquareIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleConeSquareIso,
    CategoryTheory.Functor.map_comp, moduleConeMap_eval,
    DifferentialGraded.dgModuleFunctorConeIso, asIso_hom,
    DifferentialGraded.dgModuleFunctorConeComparison_eval,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.comp_f,
    mappingCone.map, mappingCone.inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v,
    DGFunctor.moduleConeImageComparison, Category.assoc]
  erw [mappingCone.inl_v_desc_f]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
