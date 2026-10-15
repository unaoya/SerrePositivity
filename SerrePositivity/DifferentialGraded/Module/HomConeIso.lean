module
public import SerrePositivity.DifferentialGraded.Module.HomCone
public import SerrePositivity.DifferentialGraded.Complexes.ConeElements

/-! # 主Hom endはconeを複体のconeへ同型に送る -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleHomConeInverseElement (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q) :
    (mappingCone (eHomWhiskerLeft (Complex A) T f)).X q :=
  complexConeElementMk A (eHomWhiskerLeft (Complex A) T f) q
    (compose A (x := ForgetEnrichment.to (Complex A) T)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) M) (moduleConeFstElement A D f) z rfl)
    (compose A (x := ForgetEnrichment.to (Complex A) T)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) N) (moduleConeSndElement A D f) z (add_zero q))

lemma moduleHomConeInverseElement_fst_π (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) x).f (q + 1)
        ((mappingCone.fst (eHomWhiskerLeft (Complex A) T f)).val.v q (q + 1) rfl
          (moduleHomConeInverseElement A D T f q z)) =
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q z).comp
          (mappingCone.fst ((moduleEvaluation A D x).map f)).val rfl := by
  rw [moduleHomConeInverseElement, complexConeElementMk_fst, moduleHomCompose_π,
    moduleConeFstElement_π]

lemma moduleHomConeInverseElement_snd_π (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f q
        ((mappingCone.snd (eHomWhiskerLeft (Complex A) T f)).v q q (add_zero q)
          (moduleHomConeInverseElement A D T f q z)) =
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q z).comp
          (mappingCone.snd ((moduleEvaluation A D x).map f)) (add_zero q) := by
  rw [moduleHomConeInverseElement, complexConeElementMk_snd, moduleHomCompose_π,
    moduleConeSndElement_π]

lemma moduleHomConeComparison_rightInverse (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ) :
    Function.RightInverse (moduleHomConeInverseElement A D T f q)
      ((moduleHomConeComparison A D T f).f q) := by
  intro z
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f))
  intro x
  rw [moduleHomConeComparison_apply_π, moduleHomConeInverseElement_fst_π,
    moduleHomConeInverseElement_snd_π]
  apply (mappingCone.ext_cochain_to_iff ((moduleEvaluation A D x).map f) q (q + 1) rfl).2
  exact ⟨mappingCone.liftCochain_fst _ _ _ _, mappingCone.liftCochain_snd _ _ _ _⟩

lemma moduleHomConeComparison_leftInverse (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ) :
    Function.LeftInverse (moduleHomConeInverseElement A D T f q)
      ((moduleHomConeComparison A D T f).f q) := by
  intro z
  apply complexConeElement_ext A (eHomWhiskerLeft (Complex A) T f) q
  · apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
      (N := ForgetEnrichment.to (Complex A) M)
    intro x
    rw [moduleHomConeInverseElement_fst_π, moduleHomConeComparison_apply_π,
      mappingCone.liftCochain_fst]
  · apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
      (N := ForgetEnrichment.to (Complex A) N)
    intro x
    rw [moduleHomConeInverseElement_snd_π, moduleHomConeComparison_apply_π,
      mappingCone.liftCochain_snd]

lemma moduleHomConeComparison_bijective (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ) :
    Function.Bijective ((moduleHomConeComparison A D T f).f q) :=
  ⟨(moduleHomConeComparison_leftInverse A D T f q).injective,
    (moduleHomConeComparison_rightInverse A D T f q).surjective⟩

instance moduleHomConeComparison_isIso (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) : IsIso (moduleHomConeComparison A D T f) := by
  let (q : ℤ) : IsIso ((moduleHomConeComparison A D T f).f q) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (moduleHomConeComparison_bijective A D T f q)
  exact HomologicalComplex.Hom.isIso_of_components _

def moduleHomConeIso (T : ModuleCategory A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone (eHomWhiskerLeft (Complex A) T f) ≅
      moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) :=
  asIso (moduleHomConeComparison A D T f)

end SerrePositivity.DifferentialGraded
