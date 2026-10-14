module
public import SerrePositivity.PerfectComplex.Tensor
public import SerrePositivity.HomologicalAlgebra.FiniteSupportCoproduct

/-! # Bounded finite projective tensor complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory
variable {R : Type u} [CommRing R]

/-- A tensor summand is zero when its left factor is zero. -/
lemma cochainTensorSummand_isZero_left (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) (h : IsZero (P.X ij.val.1)) :
    IsZero (cochainTensorSummand P Q n ij) := by
  exact (tensorRight (Q.X ij.val.2)).map_isZero h

/-- A tensor summand is zero when its right factor is zero. -/
lemma cochainTensorSummand_isZero_right (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) (h : IsZero (Q.X ij.val.2)) :
    IsZero (cochainTensorSummand P Q n ij) := by
  exact (tensorLeft (P.X ij.val.1)).map_isZero h

/-- Projectivity of the factors implies projectivity of every total tensor degree. -/
lemma cochainTensor_projective_X (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : ∀ i, Module.Projective R (P.X i)) (hq : ∀ j, Module.Projective R (Q.X j)) (n : ℤ) :
    Module.Projective R ((cochainTensor P Q).X n) := by
  have hs : ∀ ij, Projective (cochainTensorSummand P Q n ij) := by
    intro ij
    have := hp ij.val.1
    have := hq ij.val.2
    have ht : Module.Projective R (TensorProduct R (P.X ij.val.1) (Q.X ij.val.2)) :=
      inferInstance
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : Projective ((cochainTensor P Q).X n) :=
    Projective.of_iso (cochainTensorXIso P Q n).symm
      (projective_coproduct_of_projective _ hs)
  infer_instance

/-- Boundedness leaves only finitely many nonzero summands in each total degree. -/
lemma cochainTensorSummands_finiteSupport (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hb : ∀ i, i < a ∨ b < i → IsZero (P.X i)) (n : ℤ) :
    ∃ s : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = n},
      ∀ ij, ij ∉ s → IsZero (cochainTensorSummand P Q n ij) := by
  classical
  let I := {ij : ℤ × ℤ // ij.1 + ij.2 = n}
  let e : {i // i ∈ Finset.Icc a b} ↪ I :=
    ⟨fun i => ⟨(i.val, n - i.val), by omega⟩,
      fun i j h => Subtype.ext (congrArg (fun t : I => t.val.1) h)⟩
  let s := (Finset.Icc a b).attach.map e
  have hzero : ∀ ij : I, ij ∉ s → IsZero (cochainTensorSummand P Q n ij) := by
    intro ij hi
    apply cochainTensorSummand_isZero_left
    apply hb
    by_contra hh
    have hiab : ij.val.1 ∈ Finset.Icc a b := Finset.mem_Icc.mpr (by omega)
    apply hi
    apply Finset.mem_map.mpr
    refine ⟨⟨ij.val.1, hiab⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    dsimp [e]
    apply Prod.ext
    · rfl
    · have := ij.property
      omega
  exact ⟨s, hzero⟩

/-- Every degree of a bounded tensor has an explicit finite-coproduct model. -/
lemma exists_cochainTensorX_finiteCoproductModel
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hb : ∀ i, i < a ∨ b < i → IsZero (P.X i)) (n : ℤ) :
    ∃ s : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = n},
      Nonempty ((cochainTensor P Q).X n ≅
        ∐ (fun ij : {ij // ij ∈ s} => cochainTensorSummand P Q n ij.val)) := by
  obtain ⟨s, hs⟩ := cochainTensorSummands_finiteSupport P Q a b hb n
  exact ⟨s, ⟨cochainTensorXIso P Q n ≪≫ coproductFiniteSupportIso _ s hs⟩⟩

/-- Each tensor degree is finite when the first complex is bounded and both have finite terms. -/
lemma cochainTensor_finite_X (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : ∀ i, Module.Finite R (P.X i)) (hq : ∀ j, Module.Finite R (Q.X j))
    (a b : ℤ) (hb : ∀ i, i < a ∨ b < i → IsZero (P.X i)) (n : ℤ) :
    Module.Finite R ((cochainTensor P Q).X n) := by
  classical
  obtain ⟨s, hs⟩ := cochainTensorSummands_finiteSupport P Q a b hb n
  have hS : ∀ ij, Module.Finite R (cochainTensorSummand P Q n ij) := by
    intro ij
    have := hp ij.val.1
    have := hq ij.val.2
    change Module.Finite R (TensorProduct R (P.X ij.val.1) (Q.X ij.val.2))
    infer_instance
  have : Module.Finite R (∐ cochainTensorSummand P Q n : ModuleCat.{u} R) :=
    moduleFinite_coproduct_of_finiteSupport _ s hs
  let E := (cochainTensorXIso P Q n).toLinearEquiv
  exact Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective

/-- Bounds on the factors add to give bounds on the tensor totalization. -/
lemma cochainTensor_isZero_X_of_bounds (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b c d : ℤ) (hp : ∀ i, i < a ∨ b < i → IsZero (P.X i))
    (hq : ∀ j, j < c ∨ d < j → IsZero (Q.X j)) (n : ℤ)
    (hn : n < a + c ∨ b + d < n) : IsZero ((cochainTensor P Q).X n) := by
  have hs : ∀ ij, IsZero (cochainTensorSummand P Q n ij) := by
    intro ij
    by_cases hi : ij.val.1 < a ∨ b < ij.val.1
    · exact cochainTensorSummand_isZero_left P Q n ij (hp _ hi)
    · apply cochainTensorSummand_isZero_right P Q n ij
      apply hq
      have := ij.property
      omega
  have hz : IsZero (∐ cochainTensorSummand P Q n : ModuleCat.{u} R) := by
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro ij
    exact (hs ij).eq_of_src _ _
  exact hz.of_iso (cochainTensorXIso P Q n).symm

/-- The tensor product of strictly perfect complexes is strictly perfect. -/
lemma strictlyPerfectComplex_cochainTensor (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    strictlyPerfectComplex R (cochainTensor P Q) := by
  obtain ⟨a, b, ha, hb⟩ := hp.1
  obtain ⟨c, d, hc, hd⟩ := hq.1
  have hP : ∀ i, i < a ∨ b < i → IsZero (P.X i) := fun i hi => hi.elim
    (fun h => P.isZero_of_isStrictlyGE a i h) (fun h => P.isZero_of_isStrictlyLE b i h)
  have hQ : ∀ j, j < c ∨ d < j → IsZero (Q.X j) := fun j hj => hj.elim
    (fun h => Q.isZero_of_isStrictlyGE c j h) (fun h => Q.isZero_of_isStrictlyLE d j h)
  refine ⟨⟨a + c, b + d, ?_, ?_⟩, fun n => ?_⟩
  · exact ((cochainTensor P Q).isStrictlyGE_iff (a + c)).mpr
      (fun n hn => cochainTensor_isZero_X_of_bounds P Q a b c d hP hQ n (Or.inl hn))
  · exact ((cochainTensor P Q).isStrictlyLE_iff (b + d)).mpr
      (fun n hn => cochainTensor_isZero_X_of_bounds P Q a b c d hP hQ n (Or.inr hn))
  · exact ⟨cochainTensor_finite_X P Q (fun i => (hp.2 i).1) (fun j => (hq.2 j).1) a b hP n,
      cochainTensor_projective_X P Q (fun i => (hp.2 i).2) (fun j => (hq.2 j).2) n⟩
end SerrePositivity
