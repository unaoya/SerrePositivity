module
public import SerrePositivity.DifferentialGraded.Module.ConeElements
public import SerrePositivity.DifferentialGraded.Module.Postcomposition
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor

/-! # 主Hom endにおける標準coneの行列恒等式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

def moduleConeInrElement (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X 0 :=
  (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (moduleConeInr A D f))).val

lemma moduleConeInrElement_π (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 0 (moduleConeInrElement A D f) =
      Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map f)) := by
  rw [moduleConeInrElement, ← moduleEvaluation_cochain, moduleConeInr_eval]

lemma moduleCone_inl_fst (f : M ⟶ N) :
    compose A (moduleConeFstElement A D f) (moduleConeInlElement A D f) (neg_add_cancel 1) =
      (unitElement A (ForgetEnrichment.to (Complex A) M)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeInlElement_π, moduleConeFstElement_π, yoneda_moduleUnit_π]
  exact mappingCone.inl_fst _

lemma moduleCone_inl_snd (f : M ⟶ N) :
    compose A (x := ForgetEnrichment.to (Complex A) M)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) N)
      (moduleConeSndElement A D f) (moduleConeInlElement A D f) (add_zero (-1)) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeInlElement_π, moduleConeSndElement_π, map_zero]
  exact mappingCone.inl_snd _

lemma moduleCone_inr_fst (f : M ⟶ N) :
    compose A (x := ForgetEnrichment.to (Complex A) N)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) M)
      (moduleConeFstElement A D f) (moduleConeInrElement A D f) (zero_add 1) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeInrElement_π, moduleConeFstElement_π, map_zero]
  exact mappingCone.inr_fst _

lemma moduleCone_inr_snd (f : M ⟶ N) :
    compose A (moduleConeSndElement A D f) (moduleConeInrElement A D f) (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) N)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeInrElement_π, moduleConeSndElement_π, yoneda_moduleUnit_π]
  exact mappingCone.inr_snd _

lemma moduleCone_decomposition (f : M ⟶ N) :
    compose A (moduleConeInlElement A D f) (moduleConeFstElement A D f) (add_neg_cancel 1) +
      compose A (moduleConeInrElement A D f) (moduleConeSndElement A D f) (add_zero 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) (moduleCone A D f))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [map_add, moduleHomCompose_π, moduleHomCompose_π, moduleConeInlElement_π,
    moduleConeFstElement_π, moduleConeSndElement_π, moduleConeInrElement_π, yoneda_moduleUnit_π]
  apply Cochain.ext₀
  intro n
  rw [Cochain.add_v, Cochain.comp_v _ _ _ n (n + 1) n rfl (by omega)]
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f]
  apply mappingCone.ext_to ((moduleEvaluation A D x).map f) n (n + 1) rfl <;>
    simp [Preadditive.add_comp, Category.assoc]

end SerrePositivity.DifferentialGraded
