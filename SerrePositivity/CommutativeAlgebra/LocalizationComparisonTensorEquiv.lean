module

public import SerrePositivity.CommutativeAlgebra.FinitePresentationCommonLocalizationBounds

/-! # The actual tensor maps of localization comparisons

The inverse comes from the universal property of the specified module localization.
All algebra homomorphisms remain the original coefficient extensions.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The canonical multiplication map from the base change of a specified
localization is an algebra isomorphism. -/
def localizationComparisonTensorEquiv
    {R A X : Type u} [CommRing R] [CommRing A] [CommRing X]
    [Algebra R A] [Algebra R X]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    [Algebra L X] [IsScalarTower R L X]
    (f : A →ₐ[R] X) [IsLocalizedModule S f.toLinearMap] :
    L ⊗[R] A ≃ₐ[L] X := by
  let g : L ⊗[R] A →ₐ[L] X :=
    Algebra.TensorProduct.lift (Algebra.ofId L X) f (fun _ _ => Commute.all _ _)
  let j : A →ₗ[R] L ⊗[R] A := TensorProduct.mk R L A 1
  have hcomp : (g.restrictScalars R).toLinearMap.comp j = f.toLinearMap := by
    ext a
    change algebraMap L X 1 * f a = f a
    rw [map_one, one_mul]
  let : IsLocalizedModule S ((g.restrictScalars R).toLinearMap.comp j) := by
    rw [hcomp]
    infer_instance
  have he := IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S j
    (g.restrictScalars R).toLinearMap
  have hbij : Function.Bijective g := by
    change Function.Bijective (g.restrictScalars R).toLinearMap
    rw [← he]
    exact (IsLocalizedModule.linearEquiv S j
      ((g.restrictScalars R).toLinearMap.comp j)).bijective
  exact AlgEquiv.ofBijective g hbij

/-- The isomorphism evaluates at the original tensor generators by the original map. -/
theorem localizationComparisonTensorEquiv_tmul
    {R A X : Type u} [CommRing R] [CommRing A] [CommRing X]
    [Algebra R A] [Algebra R X]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    [Algebra L X] [IsScalarTower R L X]
    (f : A →ₐ[R] X) [IsLocalizedModule S f.toLinearMap] (l : L) (a : A) :
    localizationComparisonTensorEquiv S L f (l ⊗ₜ[R] a) = algebraMap L X l * f a := rfl

/-- The tensor isomorphisms commute with the actual coefficient extension. -/
theorem localizationComparisonTensorEquiv_comp_tensorMap
    {R A B X : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing X]
    [Algebra R A] [Algebra R B] [Algebra R X]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    [Algebra L X] [IsScalarTower R L X]
    (f : A →ₐ[R] B) (w : B →ₐ[R] X)
    [IsLocalizedModule S w.toLinearMap] [IsLocalizedModule S (w.comp f).toLinearMap] :
    (localizationComparisonTensorEquiv S L w).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id L L) f) =
      (localizationComparisonTensorEquiv S L (w.comp f)).toAlgHom := by
  ext a
  change algebraMap L X 1 * w (f a) = algebraMap L X 1 * w (f a)
  rfl

/-- If a comparison and its target have the same actual localization, the
original algebra map becomes bijective on tensoring with the localization. -/
theorem localizationComparison_tensorMap_bijective
    {R A B X : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing X]
    [Algebra R A] [Algebra R B] [Algebra R X]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    [Algebra L X] [IsScalarTower R L X]
    (f : A →ₐ[R] B) (w : B →ₐ[R] X)
    [IsLocalizedModule S w.toLinearMap] [IsLocalizedModule S (w.comp f).toLinearMap] :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id L L) f) := by
  let e := localizationComparisonTensorEquiv S L w
  let e' := localizationComparisonTensorEquiv S L (w.comp f)
  have hcomp : e.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id L L) f) =
      e'.toAlgHom := localizationComparisonTensorEquiv_comp_tensorMap S L f w
  have hbij : Function.Bijective
      (e.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id L L) f)) := by
    rw [hcomp]
    exact e'.bijective
  constructor
  · intro x y hxy
    exact hbij.injective (congrArg e hxy)
  · intro y
    obtain ⟨x, hx⟩ := hbij.surjective (e y)
    exact ⟨x, e.injective hx⟩

/-- The two maps supplied by a localized splitting become bijective after
base change, for the same E,u,v,w as in the finite presentation construction. -/
theorem localizationSplitting_common_model_tensorMaps_bijective
    {R A E : Type u} [CommRing R] [CommRing A] [CommRing E]
    [Algebra R A] [Algebra R E]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L))
    (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E) (w : E →ₐ[R] (Fin r → L))
    [IsLocalizedModule S w.toLinearMap]
    (hu : ∀ a, w (u a) = e ((1 : L) ⊗ₜ[R] a))
    (hv : ∀ b i, w (v b) i = algebraMap R L (b i)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id L L) u) ∧
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id L L) v) := by
  have hu' : (w.comp u).toLinearMap = (e.restrictScalars R).toLinearEquiv.toLinearMap.comp
      (TensorProduct.mk R L A 1) := by
    apply LinearMap.ext
    intro a
    exact hu a
  let : IsLocalizedModule S (w.comp u).toLinearMap := by
    rw [hu']
    exact IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R L A 1)
      (e.restrictScalars R).toLinearEquiv
  let q := TensorProduct.piScalarRight R L L (Fin r)
  have hv' : (w.comp v).toLinearMap = (q.restrictScalars R).toLinearMap.comp
      (TensorProduct.mk R L (Fin r → R) 1) := by
    apply LinearMap.ext
    intro b
    apply funext
    intro i
    change w (v b) i = (b i) • (1 : L)
    rw [hv]
    simp only [Algebra.smul_def, mul_one]
  let : IsLocalizedModule S (w.comp v).toLinearMap := by
    rw [hv']
    exact IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R L (Fin r → R) 1)
      (q.restrictScalars R)
  exact ⟨localizationComparison_tensorMap_bijective S L u w,
    localizationComparison_tensorMap_bijective S L v w⟩

/-- The specified common-model maps identify with the original splitting and
the coordinate map under the same canonical tensor isomorphism. -/
theorem localizationSplitting_common_model_tensor_squares
    {R A E : Type u} [CommRing R] [CommRing A] [CommRing E]
    [Algebra R A] [Algebra R E]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L))
    (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E) (w : E →ₐ[R] (Fin r → L))
    [IsLocalizedModule S w.toLinearMap]
    (hu : ∀ a, w (u a) = e ((1 : L) ⊗ₜ[R] a))
    (hv : ∀ b i, w (v b) i = algebraMap R L (b i)) :
    (localizationComparisonTensorEquiv S L w).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id L L) u) = e.toAlgHom ∧
      (localizationComparisonTensorEquiv S L w).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id L L) v) =
          (Algebra.TensorProduct.piScalarRight R L L (Fin r)).toAlgHom := by
  constructor
  · ext a i
    change (1 : L) * w (u a) i = e ((1 : L) ⊗ₜ[R] a) i
    rw [one_mul]
    exact congrArg (fun z : Fin r → L => z i) (hu a)
  · ext b i
    change (1 : L) * w (v b) i = (b i) • (1 : L)
    rw [one_mul, hv]
    simp only [Algebra.smul_def, mul_one]

/-- Original R-power support bounds imply that the actual canonical map of
principal ring localizations is bijective. Neither original map is assumed
injective or surjective. -/
theorem localizationComparison_awayMap_bijective_of_power_bounds
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (d : R) (f : A →ₐ[R] B)
    (hker : ∀ a, f a = 0 → ∃ n : ℕ, d ^ n • a = 0)
    (hcoker : ∀ b : B, ∃ n : ℕ, d ^ n • b ∈ f.toLinearMap.range) :
    Function.Bijective (IsLocalization.Away.map
      (Localization.Away (algebraMap R A d))
      (Localization.Away (f (algebraMap R A d))) f.toRingHom (algebraMap R A d)) := by
  constructor
  · apply (IsLocalization.Away.map_injective_iff _ _ _).mpr
    intro a ha
    obtain ⟨n, hn⟩ := hker a ha
    exact ⟨n, by simpa only [Algebra.smul_def, map_pow] using hn⟩
  · apply (IsLocalization.Away.map_surjective_iff _ _ _ _).mpr
    intro b
    obtain ⟨n, a, ha⟩ := hcoker b
    change f a = d ^ n • b at ha
    refine ⟨a, n, ?_⟩
    change f a = f (algebraMap R A d) ^ n * b
    rw [f.commutes]
    simpa only [Algebra.smul_def, map_pow] using ha

/-- The canonical principal localization map, packaged as an R-algebra
isomorphism with the original map on the source ring. -/
def localizationComparisonAwayEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (d : R) (f : A →ₐ[R] B)
    (hker : ∀ a, f a = 0 → ∃ n : ℕ, d ^ n • a = 0)
    (hcoker : ∀ b : B, ∃ n : ℕ, d ^ n • b ∈ f.toLinearMap.range) :
    Localization.Away (algebraMap R A d) ≃ₐ[R]
      Localization.Away (f (algebraMap R A d)) :=
  AlgEquiv.ofBijective (IsLocalization.Away.mapₐ _ _ f (algebraMap R A d))
    (localizationComparison_awayMap_bijective_of_power_bounds d f hker hcoker)

/-- The principal localization isomorphism extends the specified original map. -/
theorem localizationComparisonAwayEquiv_algebraMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (d : R) (f : A →ₐ[R] B)
    (hker : ∀ a, f a = 0 → ∃ n : ℕ, d ^ n • a = 0)
    (hcoker : ∀ b : B, ∃ n : ℕ, d ^ n • b ∈ f.toLinearMap.range) (a : A) :
    localizationComparisonAwayEquiv d f hker hcoker
        (algebraMap A (Localization.Away (algebraMap R A d)) a) =
      algebraMap B (Localization.Away (f (algebraMap R A d))) (f a) := by
  change IsLocalization.Away.map _ _ f.toRingHom _ (algebraMap A _ a) = _
  exact IsLocalization.map_eq _ a

end SerrePositivity
