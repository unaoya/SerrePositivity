module
public import SerrePositivity.PerfectComplex.TensorSingle
public import SerrePositivity.HomologicalAlgebra.StupidTruncation
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Tensoring acyclic complexes with bounded flat complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

lemma cochainAcyclic_iff_support_bot (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    P.Acyclic ↔ HasHomologySupportOn (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R)) P := by
  rw [hasHomologySupportOn_bot_iff]
  exact forall_congr' (fun i => HomologicalComplex.exactAt_iff_isZero_homology P i)

lemma cochainAcyclic_of_iso {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : P.Acyclic) (e : P ≅ Q) : Q.Acyclic :=
  (cochainAcyclic_iff_support_bot Q).mpr
    (((cochainAcyclic_iff_support_bot P).mp hP).of_iso e)

lemma cochainAcyclic_shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : P.Acyclic) (n : ℤ) : (P⟦n⟧).Acyclic :=
  (cochainAcyclic_iff_support_bot _).mpr
    (((cochainAcyclic_iff_support_bot P).mp hP).shift n)

lemma cochainAcyclic_of_shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (n : ℤ) (hP : (P⟦n⟧).Acyclic) : P.Acyclic :=
  cochainAcyclic_of_iso (cochainAcyclic_shift hP (-n)) (shiftShiftNeg P n)

lemma cochainAcyclic_mappingCone {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hP : P.Acyclic) (hQ : Q.Acyclic) :
    (CochainComplex.mappingCone f).Acyclic :=
  (cochainAcyclic_iff_support_bot _).mpr
    (((cochainAcyclic_iff_support_bot P).mp hP).mappingCone f
      ((cochainAcyclic_iff_support_bot Q).mp hQ))

/-- A degreewise split sequence propagates tensor acyclicity from outer to middle terms. -/
lemma cochainTensor_acyclic_of_degreewiseSplit
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (h₁ : (cochainTensor S.X₁ P).Acyclic) (h₃ : (cochainTensor S.X₃ P).Acyclic) :
    (cochainTensor S.X₂ P).Acyclic := by
  let f := CochainComplex.homOfDegreewiseSplit S σ
  have hshift : (cochainTensor (S.X₁⟦(1 : ℤ)⟧) P).Acyclic :=
    cochainAcyclic_of_iso (cochainAcyclic_shift h₁ 1) (cochainTensorShiftLeft S.X₁ P 1).symm
  have hc := cochainAcyclic_mappingCone (cochainTensorMap f (𝟙 P)) h₃ hshift
  have ht : (cochainTensor (CochainComplex.mappingCone f) P).Acyclic :=
    cochainAcyclic_of_iso hc (cochainTensorConeLeft f P).symm
  let e := CochainComplex.mappingConeHomOfDegreewiseSplitIso S σ
  have he : (cochainTensor (S.X₂⟦(1 : ℤ)⟧) P).Acyclic :=
    (cochainAcyclic_iff_support_bot _).mpr
      (((cochainAcyclic_iff_support_bot _).mp ht).of_homotopyEquiv
        (cochainTensorHomotopyEquiv (HomotopyEquiv.ofIso e) (HomotopyEquiv.refl P)))
  exact cochainAcyclic_of_shift 1 (cochainAcyclic_of_iso he (cochainTensorShiftLeft S.X₂ P 1))

/-- A complex concentrated in degree zero is isomorphic to its single nonzero term. -/
def cochainIsoSingleZero (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hQ : ∀ i : ℤ, i ≠ 0 → IsZero (Q.X i)) : Q ≅ cochainSingleZero (Q.X 0) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => by
    by_cases hi : i = 0
    · subst i
      exact (singleObjXSelf (.up ℤ) 0 (Q.X 0)).symm
    · exact (hQ i hi).iso (isZero_single_obj_X _ _ _ i hi)) (by
      intro i j hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := by dsimp at hij; omega
        exact (isZero_single_obj_X (.up ℤ) 0 (Q.X 0) j hj).eq_of_tgt _ _
      · exact (hQ i hi).eq_of_src _ _)

lemma cochainTensor_concentratedZero_acyclic
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hQ : ∀ i : ℤ, i ≠ 0 → IsZero (Q.X i)) [Module.Flat R (Q.X 0)] (hP : P.Acyclic) :
    (cochainTensor Q P).Acyclic := by
  have h := cochainTensorSingleLeft_acyclic (Q.X 0) P hP
  exact (cochainAcyclic_iff_support_bot _).mpr
    (((cochainAcyclic_iff_support_bot _).mp h).of_homotopyEquiv
      (cochainTensorHomotopyEquiv (HomotopyEquiv.ofIso (cochainIsoSingleZero Q hQ).symm)
        (HomotopyEquiv.refl P)))

/-- A complex with one flat term in any degree preserves acyclicity under tensor. -/
lemma cochainTensor_concentrated_acyclic
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (hQ : ∀ i : ℤ, i ≠ a → IsZero (Q.X i)) [Module.Flat R (Q.X a)] (hP : P.Acyclic) :
    (cochainTensor Q P).Acyclic := by
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero ((Q⟦a⟧).X i) :=
    (Q.shiftFunctorObjXIso a i (i + a) rfl).isZero_iff.mpr (hQ (i + a) (by omega))
  have : Module.Flat R ((Q⟦a⟧).X 0) :=
    Module.Flat.of_linearEquiv (Q.shiftFunctorObjXIso a 0 a (by omega)).toLinearEquiv
  have h := cochainTensor_concentratedZero_acyclic (Q⟦a⟧) P hz hP
  exact cochainAcyclic_of_shift a (cochainAcyclic_of_iso h (cochainTensorShiftLeft Q P a))

/-- A bounded complex of flat modules preserves acyclicity of any other complex. -/
lemma cochainTensor_acyclic_of_flat_bounds
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hQa : ∀ i, i < a → IsZero (Q.X i))
    (hQb : ∀ i, b < i → IsZero (Q.X i))
    (hflat : ∀ i, Module.Flat R (Q.X i)) (hP : P.Acyclic) :
    (cochainTensor Q P).Acyclic := by
  have H : ∀ n : ℕ, ∀ (Q : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ),
      (∀ i, i < a → IsZero (Q.X i)) →
      (∀ i, a + n < i → IsZero (Q.X i)) →
      (∀ i, Module.Flat R (Q.X i)) → (cochainTensor Q P).Acyclic := by
    intro n
    induction n with
    | zero =>
      intro Q a ha hb hf
      have hz (i : ℤ) (hi : i ≠ a) : IsZero (Q.X i) := by
        by_cases hia : i < a
        · exact ha i hia
        · exact hb i (by simp; omega)
      have := hf a
      exact cochainTensor_concentrated_acyclic Q P a hz hP
    | succ n ih =>
      intro Q a ha hb hf
      let S := StupidTruncation.shortComplex Q (a + 1)
      have h₁a (i : ℤ) (hi : i < a + 1) : IsZero (S.X₁.X i) :=
        StupidTruncation.above_isZero_X Q (a + 1) i hi
      have h₁b (i : ℤ) (hi : a + 1 + n < i) : IsZero (S.X₁.X i) := by
        have hge : a + 1 ≤ i := by omega
        exact (StupidTruncation.aboveXIso Q (a + 1) i hge).isZero_iff.mpr
          (hb i (by push_cast; omega))
      have h₁flat (i : ℤ) : Module.Flat R (S.X₁.X i) := by
        by_cases hge : a + 1 ≤ i
        · have := hf i
          exact Module.Flat.of_linearEquiv
            (StupidTruncation.aboveXIso Q (a + 1) i hge).toLinearEquiv
        · have := ModuleCat.subsingleton_of_isZero (h₁a i (by omega))
          infer_instance
      have h₁ := ih S.X₁ (a + 1) h₁a h₁b h₁flat
      have h₃zero (i : ℤ) (hi : i ≠ a) : IsZero (S.X₃.X i) := by
        by_cases hia : i < a
        · exact (StupidTruncation.belowXIso Q (a + 1 - 1) i (by omega)).isZero_iff.mpr (ha i hia)
        · exact StupidTruncation.below_isZero_X Q (a + 1 - 1) i (by omega)
      have : Module.Flat R (S.X₃.X a) := by
        have := hf a
        exact Module.Flat.of_linearEquiv (StupidTruncation.belowXIso Q (a + 1 - 1) a
          (by omega)).toLinearEquiv
      have h₃ := cochainTensor_concentrated_acyclic S.X₃ P a h₃zero hP
      exact cochainTensor_acyclic_of_degreewiseSplit S
        (StupidTruncation.splitting Q (a + 1)) P h₁ h₃
  exact H (b - a).toNat Q a hQa (fun i hi => hQb i (by omega)) hflat

/-- A cochain map is a quasi-isomorphism precisely when its concrete cone is acyclic. -/
lemma cochain_quasiIso_iff_cone_acyclic
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P') :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

/-- A bounded flat right factor preserves quasi-isomorphisms in an arbitrary left factor. -/
lemma cochainTensor_quasiIso_left_of_boundedFlat
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hQa : ∀ i, i < a → IsZero (Q.X i)) (hQb : ∀ i, b < i → IsZero (Q.X i))
    (hflat : ∀ i, Module.Flat R (Q.X i)) (f : P ⟶ P') [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 Q)) := by
  have hc := (cochain_quasiIso_iff_cone_acyclic f).mp inferInstance
  have ht := cochainTensor_acyclic_of_flat_bounds Q (CochainComplex.mappingCone f)
    a b hQa hQb hflat hc
  have ht' := cochainAcyclic_of_iso ht (cochainTensorSymmetry Q (CochainComplex.mappingCone f))
  exact (cochain_quasiIso_iff_cone_acyclic _).mpr
    (cochainAcyclic_of_iso ht' (cochainTensorConeLeft f Q))

/-- A strictly perfect right factor preserves arbitrary quasi-isomorphisms. -/
lemma cochainTensor_quasiIso_left_of_perfect
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (hq : strictlyPerfectComplex R Q)
    (f : P ⟶ P') [QuasiIso f] : QuasiIso (cochainTensorMap f (𝟙 Q)) := by
  obtain ⟨a, b, ha, hb⟩ := hq.1
  apply cochainTensor_quasiIso_left_of_boundedFlat Q a b
    (fun i hi => Q.isZero_of_isStrictlyGE a i hi)
    (fun i hi => Q.isZero_of_isStrictlyLE b i hi)
  intro i
  have := (hq.2 i).2
  infer_instance
end SerrePositivity
