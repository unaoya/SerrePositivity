module
public import SerrePositivity.DifferentialGraded.Module.GradedSplitElements
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor

/-! # 全次数分裂の次数零Hom要素による行列恒等式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉零加群射に対応する全Hom endの零次数cycle。 -/
abbrev endomorphismClosedElement {M N : ModuleCategory A D} (f : M ⟶ N) :=
  (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val

lemma endomorphismClosedElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) x).f 0 (endomorphismClosedElement A D f) =
        Cochain.ofHom ((moduleEvaluation A D x).map f) :=
  (moduleEvaluation_cochain A D x f).symm

variable {A D} {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

lemma gradedSplit_inclusion_retraction_element (s : ModuleGradedSplit A D f g) :
    forward A (endomorphismClosedElement A D f) s.retractionElement (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) M)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomForward_π, endomorphismClosedElement_π, s.retractionElement_π,
    yoneda_moduleUnit_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  apply Cochain.ext₀
  intro n
  rw [Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n)]
  simp only [Cochain.ofHom_v, Cochain.ofHoms_v, id_f]
  exact s.inclusion_retraction x n

lemma gradedSplit_section_projection_element (s : ModuleGradedSplit A D f g) :
    forward A s.sectionElement (endomorphismClosedElement A D g) (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) P)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomForward_π, s.sectionElement_π, endomorphismClosedElement_π,
    yoneda_moduleUnit_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  apply Cochain.ext₀
  intro n
  rw [Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n)]
  simp only [Cochain.ofHom_v, Cochain.ofHoms_v, id_f]
  exact s.section_projection x n

lemma gradedSplit_section_retraction_element (s : ModuleGradedSplit A D f g) :
    forward A (D := RightModule A D) (x := ForgetEnrichment.to (Complex A) P)
      (y := ForgetEnrichment.to (Complex A) N) (z := ForgetEnrichment.to (Complex A) M)
      s.sectionElement s.retractionElement (zero_add 0) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomForward_π, s.sectionElement_π, s.retractionElement_π, map_zero]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  apply Cochain.ext₀
  intro n
  rw [Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n)]
  simp only [Cochain.ofHoms_v, Cochain.zero_v]
  exact s.section_retraction x n

lemma gradedSplit_decomposition_element (s : ModuleGradedSplit A D f g) :
    forward A s.retractionElement (endomorphismClosedElement A D f) (zero_add 0) +
      forward A (endomorphismClosedElement A D g) s.sectionElement (zero_add 0) =
        (unitElement A (ForgetEnrichment.to (Complex A) N)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [map_add, moduleHomForward_π, moduleHomForward_π, s.retractionElement_π,
    s.sectionElement_π, endomorphismClosedElement_π, endomorphismClosedElement_π,
    yoneda_moduleUnit_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  apply Cochain.ext₀
  intro n
  rw [Cochain.add_v, Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n),
    Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n)]
  simp only [Cochain.ofHom_v, Cochain.ofHoms_v, id_f]
  exact s.decomposition x n

end SerrePositivity.DifferentialGraded
