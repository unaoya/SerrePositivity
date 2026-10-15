module
public import SerrePositivity.DifferentialGraded.Module.HomotopyConeTriangle
public import SerrePositivity.DifferentialGraded.Module.Zero

/-! # 恒等射のconeの全dg自然な収縮 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomCycle_zero (M N : ModuleCategory A D) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (0 : M ⟶ N))).val =
      (0 : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N)).X 0) := by
  apply moduleHomElement_ext A D
  intro x
  rw [← moduleEvaluation_cochain, CategoryTheory.Functor.map_zero, Cochain.ofHom_zero, map_zero]

def moduleConeInlHomotopy {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleHomotopy A D (f ≫ moduleConeInr A D f) 0 :=
  ⟨moduleConeInlElement A D f, by
    change (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-1) 0
        (moduleConeInlElement A D f) = _
    rw [moduleConeInlElement_d, moduleHomCycle_zero, sub_zero]⟩

def moduleConeIdContractingElement (M : ModuleCategory A D) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
    (y := ForgetEnrichment.to (Complex A) M)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
    (moduleConeInlElement A D (𝟙 M)) (moduleConeSndElement A D (𝟙 M)) (by omega)

lemma moduleConeIdContractingElement_π (M : ModuleCategory A D) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M))) x).f (-1)
        (moduleConeIdContractingElement A D M) =
      (mappingCone.snd ((moduleEvaluation A D x).map (𝟙 M))).comp
        (mappingCone.inl ((moduleEvaluation A D x).map (𝟙 M))) (zero_add (-1)) := by
  rw [moduleConeIdContractingElement, moduleHomCompose_π,
    moduleConeInlElement_π, moduleConeSndElement_π]

lemma moduleConeIdContractingElement_d (M : ModuleCategory A D) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))).d (-1) 0
        (moduleConeIdContractingElement A D M) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (𝟙 (moduleCone A D (𝟙 M))))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeIdContractingElement_π,
    ← moduleEvaluation_cochain]
  rw [(moduleEvaluation A D x).map_id (moduleCone A D (𝟙 M))]
  change δ (-1) 0
    ((mappingCone.snd ((moduleEvaluation A D x).map (𝟙 M))).comp
      (mappingCone.inl ((moduleEvaluation A D x).map (𝟙 M))) (zero_add (-1))) =
        Cochain.ofHom (𝟙 (mappingCone ((moduleEvaluation A D x).map (𝟙 M))))
  rw [CategoryTheory.Functor.map_id]
  let K := (moduleEvaluation A D x).obj M
  let h := (Cochain.equivHomotopy _ _) (mappingCone.homotopyToZeroOfId K)
  have hc : h.val = (mappingCone.snd (𝟙 K)).comp (mappingCone.inl (𝟙 K)) (zero_add (-1)) := by
    simp [h, mappingCone.homotopyToZeroOfId, mappingCone.descHomotopy, mappingCone.descCochain]
  have hd := h.property
  rw [hc, Cochain.ofHom_zero, add_zero] at hd
  exact hd.symm

def moduleConeIdHomotopy (M : ModuleCategory A D) :
    ModuleHomotopy A D (𝟙 (moduleCone A D (𝟙 M))) 0 :=
  ⟨moduleConeIdContractingElement A D M, by
    change (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))).d (-1) 0
        (moduleConeIdContractingElement A D M) = _
    rw [moduleConeIdContractingElement_d, moduleHomCycle_zero, sub_zero]⟩


lemma moduleConeId_isZero (M : ModuleCategory A D) :
    IsZero ((moduleToHomotopy A D).obj (moduleCone A D (𝟙 M))) := by
  apply (IsZero.iff_id_eq_zero _).2
  have h := (moduleToHomotopy_map_eq_iff A D
    (𝟙 (moduleCone A D (𝟙 M))) 0).2 ⟨moduleConeIdHomotopy A D M⟩
  simpa only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] using h

instance moduleHomotopyHasZeroObject : HasZeroObject (ModuleHomotopyCategory A D) :=
  ((moduleToHomotopy A D).map_isZero (isZero_zero (ModuleCategory A D))).hasZeroObject

end SerrePositivity.DifferentialGraded
