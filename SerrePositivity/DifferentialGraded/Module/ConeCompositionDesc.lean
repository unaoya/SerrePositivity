module
public import SerrePositivity.DifferentialGraded.Module.ConeCompositionInputs
public import SerrePositivity.DifferentialGraded.Complexes.ConeCompositionDesc

/-! # 合成cone比較の全dg自然な逆方向射 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeCompInnerElement {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) M)
    (y := ForgetEnrichment.to (Complex A) N)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D g))
    (moduleConeInlElement A D g)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (zero_add (-1))

def moduleConeCompOuterElement {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (y := ForgetEnrichment.to (Complex A) N)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D g))
    (moduleConeInlElement A D g) (moduleConeSndElement A D f) (zero_add (-1))

lemma moduleConeCompInnerElement_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g)) x).f (-1)
        (moduleConeCompInnerElement A D f g) =
      (Cochain.ofHom ((moduleEvaluation A D x).map f)).comp
        (mappingCone.inl ((moduleEvaluation A D x).map g)) (zero_add (-1)) := by
  rw [moduleConeCompInnerElement, moduleHomCompose_π,
    ← moduleEvaluation_cochain, moduleConeInlElement_π]

lemma moduleConeCompOuterElement_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D g)) x).f (-1)
        (moduleConeCompOuterElement A D f g) =
      (mappingCone.snd ((moduleEvaluation A D x).map f)).comp
        (mappingCone.inl ((moduleEvaluation A D x).map g)) (zero_add (-1)) := by
  rw [moduleConeCompOuterElement, moduleHomCompose_π,
    moduleConeSndElement_π, moduleConeInlElement_π]

lemma moduleConeCompInnerElement_d {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
        (moduleConeCompInnerElement A D f g) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        ((f ≫ g) ≫ moduleConeInr A D g))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeCompInnerElement_π, ← moduleEvaluation_cochain,
    (moduleEvaluation A D x).map_comp (f ≫ g) (moduleConeInr A D g), moduleConeInr_eval]
  exact complexConeComp_inner_boundary ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleEvaluation A D x).map_comp f g)

def moduleConeCompInnerDesc {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D (f ≫ g) ⟶ moduleCone A D g :=
  moduleConeDescOfBoundary A D (f ≫ g) (moduleConeCompInnerElement A D f g)
    (moduleConeInr A D g) (moduleConeCompInnerElement_d A D f g)

lemma moduleConeCompInnerDesc_cochain {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    Cochain.ofHom ((moduleEvaluation A D x).map (moduleConeCompInnerDesc A D f g)) =
      mappingCone.descCochain ((moduleEvaluation A D x).map (f ≫ g))
        ((Cochain.ofHom ((moduleEvaluation A D x).map f)).comp
          (mappingCone.inl ((moduleEvaluation A D x).map g)) (zero_add (-1)))
        (Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map g))) (neg_add_cancel 1) := by
  unfold moduleConeCompInnerDesc
  rw [moduleConeDescOfBoundary_eval, mappingCone.ofHom_desc]
  change mappingCone.descCochain ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g)) x).f (-1)
        (moduleConeCompInnerElement A D f g))
    (Cochain.ofHom ((moduleEvaluation A D x).map (moduleConeInr A D g))) (neg_add_cancel 1) = _
  rw [moduleConeCompInnerElement_π, moduleConeInr_eval]

lemma moduleConeCompOuterElement_d {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
        (moduleConeCompOuterElement A D f g) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeCompMap A D f g ≫ moduleConeCompInnerDesc A D f g))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeCompOuterElement_π, ← moduleEvaluation_cochain,
    (moduleEvaluation A D x).map_comp, Cochain.ofHom_comp, moduleConeCompInnerDesc_cochain]
  have h := complexConeComp_outer_boundary ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleEvaluation A D x).map_comp f g)
    ((moduleEvaluation A D x).map (moduleConeCompMap A D f g)) (moduleConeCompMap_eval A D f g x)
  rw [Cochain.ofHom_comp, mappingCone.ofHom_desc] at h
  exact h

/-- cone(cone(f)→cone(f≫g))からcone(g)への全dg自然な逆方向比較。 -/
def moduleConeCompInv {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D (moduleConeCompMap A D f g) ⟶ moduleCone A D g :=
  moduleConeDescOfBoundary A D (moduleConeCompMap A D f g)
    (moduleConeCompOuterElement A D f g) (moduleConeCompInnerDesc A D f g)
    (moduleConeCompOuterElement_d A D f g)

@[simp] lemma moduleConeCompInv_eval {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleEvaluation A D x).map (moduleConeCompInv A D f g) =
      (complexConeCompHomotopyEquiv ((moduleEvaluation A D x).map f)
        ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
        ((moduleEvaluation A D x).map_comp f g)
        ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
        (moduleConeCompMap_eval A D f g x)).inv := by
  unfold moduleConeCompInv
  rw [moduleConeDescOfBoundary_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_desc, complexConeComp_inv_cochain]
  rw [moduleConeCompOuterElement_π, moduleConeCompInnerDesc_cochain]

lemma moduleConeComp_hom_inv {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleConeCompHom A D f g ≫ moduleConeCompInv A D f g = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeCompHom_eval, moduleConeCompInv_eval,
    complexConeComp_hom_inv, CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.DifferentialGraded
