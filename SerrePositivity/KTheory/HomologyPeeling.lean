module
public import SerrePositivity.KTheory.HomologyEuler
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Peeling the top homology of a strictly perfect complex

Good truncation is used only as an intermediate target. K-projectivity lifts
its quasi-inverse, so its terms need not be projective.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A perfect complex with no positive homology maps to its H⁰ with identity on H⁰. -/
lemma exists_topHomologyMap (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hpos : ∀ i : ℤ, 0 < i → IsZero (P.homology i)) :
    ∃ g : P ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj (P.homology 0),
      homologyMap g 0 ≫ (singleObjHomologySelfIso _ 0 (P.homology 0)).hom = 𝟙 _ := by
  have : P.IsKProjective := strictlyPerfectComplex_isKProjective hp
  have : P.IsLE 0 := (P.isLE_iff 0).mpr
    (fun i hi => (P.exactAt_iff_isZero_homology i).mpr (hpos i hi))
  let Q := P.truncLE 0
  let i := P.ιTruncLE 0
  have : QuasiIso i := (P.quasiIso_ιTruncLE_iff 0).mpr inferInstance
  obtain ⟨f, ⟨H⟩⟩ := exists_lift_of_quasiIso i (𝟙 P)
  have htop : ∀ j : ℤ, 0 < j → IsZero (Q.X j) := fun j hj => Q.isZero_of_isStrictlyLE 0 j hj
  let a := toSingleOfHomology Q (d_zero_one_eq_zero Q htop) (homologyMap i 0)
  refine ⟨f ≫ a, ?_⟩
  have ha := toSingleOfHomology_homologyMap Q (d_zero_one_eq_zero Q htop) (homologyMap i 0)
  rw [homologyMap_comp, Category.assoc, ha, ← homologyMap_comp, H.homologyMap_eq, homologyMap_id]

variable [IsNoetherianRing R] [HasFiniteProjectiveResolutions R]
/-- Lift the top-homology map to a perfect resolution, making H⁰ an isomorphism. -/
lemma exists_topResolutionMap (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hpos : ∀ i : ℤ, 0 < i → IsZero (P.homology i)) :
    ∃ (F : PerfectModuleResolution (P.homology 0)) (l : P ⟶ F.complex),
      homologyMap l 0 ≫ F.resolution.homologyZeroIso.hom = 𝟙 _ := by
  have := (hp.2 0).1
  have : Module.Finite R (P.homology 0) := homology_moduleFinite P 0
  let F := chosenPerfectModuleResolution (P.homology 0)
  obtain ⟨g, hg⟩ := exists_topHomologyMap P hp hpos
  have : P.IsKProjective := strictlyPerfectComplex_isKProjective hp
  obtain ⟨l, ⟨H⟩⟩ := exists_lift_of_quasiIso F.augmentation g
  refine ⟨F, l, ?_⟩
  have ha := toSingleOfHomology_homologyMap F.complex
    (d_zero_one_eq_zero _ F.resolution.isZero_X) F.resolution.homologyZeroIso.hom
  calc
    homologyMap l 0 ≫ F.resolution.homologyZeroIso.hom =
        homologyMap l 0 ≫ homologyMap F.augmentation 0 ≫
          (singleObjHomologySelfIso _ 0 (P.homology 0)).hom := by
      simpa only [PerfectModuleResolution.augmentation, Category.assoc] using
        congrArg (fun k => homologyMap l 0 ≫ k) ha.symm
    _ = homologyMap g 0 ≫ (singleObjHomologySelfIso _ 0 (P.homology 0)).hom := by
      rw [← Category.assoc, ← homologyMap_comp, H.homologyMap_eq]
    _ = 𝟙 _ := hg

omit [IsNoetherianRing R] [HasFiniteProjectiveResolutions R] in
/-- Peeling H⁰ decreases the homology interval even if the terms of the cone grow. -/
lemma topResolutionCone_homology_bounded
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (hbelow : ∀ i : ℤ, i < a → IsZero (P.homology i))
    (hpos : ∀ i : ℤ, 0 < i → IsZero (P.homology i))
    (F : PerfectModuleResolution (P.homology 0)) (l : P ⟶ F.complex)
    (hl : homologyMap l 0 ≫ F.resolution.homologyZeroIso.hom = 𝟙 _) :
    ∀ i : ℤ, i < a - 1 ∨ -2 < i → IsZero ((CochainComplex.mappingCone l).homology i) := by
  have he : homologyMap l 0 = F.resolution.homologyZeroIso.inv := by
    apply (cancel_mono F.resolution.homologyZeroIso.hom).mp
    rw [hl, Iso.inv_hom_id]
  have : IsIso (homologyMap l 0) := by rw [he]; infer_instance
  intro i hi
  by_cases hi' : i = -1
  · subst i
    have h10 : (-1 : ℤ) + 1 = 0 := by norm_num
    have hδ : Cone.δ l (-1) 0 h10 = 0 :=
      (Cone.exact₁ l (-1) 0 h10).mono_g_iff.mp inferInstance
    exact (Cone.exact₃ l (-1) 0 h10).isZero_X₂
      ((F.resolution.isZero_homology (-1) (by norm_num)).eq_zero_of_src _) hδ
  · by_cases hi0 : i = 0
    · subst i
      have hι : homologyMap (CochainComplex.mappingCone.inr l) 0 = 0 :=
        (Cone.exact₂ l 0).epi_f_iff.mp inferInstance
      exact (Cone.exact₃ l 0 1 rfl).isZero_X₂ hι ((hpos 1 one_pos).eq_zero_of_tgt _)
    · apply (Cone.exact₃ l i (i + 1) rfl).isZero_of_both_isZero
      · exact F.resolution.isZero_homology i hi0
      · rcases hi with hi | hi
        · exact hbelow _ (by omega)
        · exact hpos _ (by omega)

end SerrePositivity
