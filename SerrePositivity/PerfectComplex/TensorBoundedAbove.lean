module
public import SerrePositivity.PerfectComplex.TensorAcyclic

/-! # Tensoring bounded-above flat complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Only maps on the diagonal contributing to a total degree need be invertible. -/
lemma cochainTensorMap_f_isIso_of_diagonal
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (n : ℤ)
    (h : ∀ i j : ℤ, i + j = n → IsIso (f.f i ⊗ₘ g.f j)) :
    IsIso ((cochainTensorMap f g).f n) := by
  let v : (cochainTensor P' Q').X n ⟶ (cochainTensor P Q).X n :=
    HomologicalComplex₂.totalDesc _ (fun i j hij =>
      have := h i j hij
      inv (f.f i ⊗ₘ g.f j) ≫ ιTensorObj P Q i j n hij)
  refine ⟨⟨v, ?_, ?_⟩⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    have := h i j hij
    simp only [v, ι_mapBifunctorMap_assoc,
      HomologicalComplex₂.ι_totalDesc, Category.comp_id,
      curriedTensor_map_app, curriedTensor_obj_map]
    simpa only [tensorHom_def, Category.assoc] using
      (IsIso.hom_inv_id_assoc (f.f i ⊗ₘ g.f j) (ιTensorObj P Q i j n hij))
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    have := h i j hij
    simp [v, ι_mapBifunctorMap, tensorHom_def]

/-- Lower truncation preserves a tensor degree if the other factor vanishes above. -/
lemma cochainTensor_truncation_f_isIso
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ) (a b n : ℤ)
    (hP : ∀ j, b < j → IsZero (P.X j)) (hn : a + b ≤ n) :
    IsIso ((cochainTensorMap (StupidTruncation.inclusion Q a) (𝟙 P)).f n) := by
  apply cochainTensorMap_f_isIso_of_diagonal
  intro i j hij
  by_cases hi : a ≤ i
  · have := StupidTruncation.inclusion_f_isIso Q a i hi
    change IsIso ((StupidTruncation.inclusion Q a).f i ⊗ₘ 𝟙 (P.X j))
    infer_instance
  · have hz := hP j (by omega)
    exact ((tensorLeft ((StupidTruncation.above Q a).X i)).map_isZero hz).isIso
      ((tensorLeft (Q.X i)).map_isZero hz) _

/-- A bounded-above flat complex preserves acyclicity of bounded-above complexes.
No lower bound or finite projective dimension is required. -/
lemma cochainTensor_acyclic_of_flat_boundedAbove
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ) (bQ bP : ℤ)
    (hQ : ∀ i, bQ < i → IsZero (Q.X i))
    (hP : ∀ i, bP < i → IsZero (P.X i))
    (hflat : ∀ i, Module.Flat R (Q.X i)) (hacyclic : P.Acyclic) :
    (cochainTensor Q P).Acyclic := by
  intro n
  let a := n - 1 - bP
  let T := StupidTruncation.above Q a
  have hTa (i : ℤ) (hi : i < a) : IsZero (T.X i) :=
    StupidTruncation.above_isZero_X Q a i hi
  have hTb (i : ℤ) (hi : bQ < i) : IsZero (T.X i) := by
    by_cases hai : a ≤ i
    · exact (StupidTruncation.aboveXIso Q a i hai).isZero_iff.mpr (hQ i hi)
    · exact hTa i (by omega)
  have hTf (i : ℤ) : Module.Flat R (T.X i) := by
    by_cases hai : a ≤ i
    · have := hflat i
      exact Module.Flat.of_linearEquiv (StupidTruncation.aboveXIso Q a i hai).toLinearEquiv
    · have := ModuleCat.subsingleton_of_isZero (hTa i (by omega))
      infer_instance
  have hac := cochainTensor_acyclic_of_flat_bounds T P a bQ hTa hTb hTf hacyclic
  let f := cochainTensorMap (StupidTruncation.inclusion Q a) (𝟙 P)
  have hf (q : ℤ) (hq : n - 1 ≤ q) : IsIso (f.f q) :=
    cochainTensor_truncation_f_isIso Q P a bP q hP (by dsimp [a]; omega)
  have hqi : QuasiIsoAt f n := by
    rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
    let t := (shortComplexFunctor' (ModuleCat.{u} R) (.up ℤ) (n - 1) n (n + 1)).map f
    have : IsIso t.τ₁ := hf (n - 1) (by omega)
    have : IsIso t.τ₂ := hf n (by omega)
    have : IsIso t.τ₃ := hf (n + 1) (by omega)
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono t
  exact (quasiIsoAt_iff_exactAt f n (hac n)).mp hqi

/-- A bounded-above flat right factor preserves quasi-isomorphisms between
bounded-above complexes. -/
lemma cochainTensor_quasiIso_left_of_boundedAboveFlat
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (bQ bP bP' : ℤ)
    (hQ : ∀ i, bQ < i → IsZero (Q.X i))
    (hP : ∀ i, bP < i → IsZero (P.X i))
    (hP' : ∀ i, bP' < i → IsZero (P'.X i))
    (hflat : ∀ i, Module.Flat R (Q.X i)) (f : P ⟶ P') [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 Q)) := by
  have hc := (cochain_quasiIso_iff_cone_acyclic f).mp inferInstance
  have hb (i : ℤ) (hi : max bP bP' < i) :
      IsZero ((CochainComplex.mappingCone f).X i) := by
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hP (i + 1) (by omega), hP' i (by omega)⟩
  have ht := cochainTensor_acyclic_of_flat_boundedAbove Q
    (CochainComplex.mappingCone f) bQ (max bP bP') hQ hb hflat hc
  have ht' := cochainAcyclic_of_iso ht (cochainTensorSymmetry Q (CochainComplex.mappingCone f))
  exact (cochain_quasiIso_iff_cone_acyclic _).mpr
    (cochainAcyclic_of_iso ht' (cochainTensorConeLeft f Q))

end SerrePositivity
