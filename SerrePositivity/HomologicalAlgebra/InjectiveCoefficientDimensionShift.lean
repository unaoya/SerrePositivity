module
public import SerrePositivity.HomologicalAlgebra.CoefficientDimensionShift
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Natural dimension shifting through chosen injective embeddings -/
@[expose] public noncomputable section
universe v u v' u'
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The short exact sequence associated to the chosen injective embedding. -/
abbrev injectiveCoefficientSequence (M : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (by simp)

lemma injectiveCoefficientSequence_shortExact (M : C) :
    (injectiveCoefficientSequence M).ShortExact where
  exact := ShortComplex.exact_cokernel _

/-- Any coefficient map extends to a map of the chosen short exact sequences.
The extensions are not asserted to form a functor. -/
def injectiveCoefficientSequenceMap {M N : C} (f : M ⟶ N) :
    injectiveCoefficientSequence M ⟶ injectiveCoefficientSequence N where
  τ₁ := f
  τ₂ := Injective.factorThru (f ≫ Injective.ι N) (Injective.ι M)
  τ₃ := cokernel.map _ _ f
    (Injective.factorThru (f ≫ Injective.ι N) (Injective.ι M)) (by simp)
  comm₁₂ := by simp [injectiveCoefficientSequence]
  comm₂₃ := by simp [injectiveCoefficientSequence]

variable (F G : C ⥤ CochainComplex D ℕ)
variable [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Exact coefficient functors preserve the chosen injective short exact sequence. -/
lemma injectiveCoefficientSequence_map_shortExact (M : C) :
    ((injectiveCoefficientSequence M).map F).ShortExact :=
  (injectiveCoefficientSequence_shortExact M).map_of_exact F

/-- Lift a natural homology comparison by one degree using positive acyclicity
on injective coefficients. The construction also handles the first step. -/
def injectiveCoefficientHomologyStep (n : ℕ)
    (hF : ∀ J : C, Injective J → IsZero ((F.obj J).homology (n + 1)))
    (hG : ∀ J : C, Injective J → IsZero ((G.obj J).homology (n + 1)))
    (e : F ⋙ homologyFunctor D (.up ℕ) n ≅ G ⋙ homologyFunctor D (.up ℕ) n) :
    F ⋙ homologyFunctor D (.up ℕ) (n + 1) ≅
      G ⋙ homologyFunctor D (.up ℕ) (n + 1) :=
  NatIso.ofComponents (fun M => coefficientDimensionShiftIso
    (injectiveCoefficientSequence_map_shortExact F M) n
    (injectiveCoefficientSequence_map_shortExact G M)
    (hF (Injective.under M) inferInstance) (hG (Injective.under M) inferInstance)
    (e.app (Injective.under M)) (e.app (cokernel (Injective.ι M)))
    (e.hom.naturality (cokernel.π (Injective.ι M)))) (by
      intro M N f
      apply coefficientDimensionShift_naturality
        (injectiveCoefficientSequence_map_shortExact F M) n
        (injectiveCoefficientSequence_map_shortExact F N)
        (injectiveCoefficientSequence_map_shortExact G M)
        (injectiveCoefficientSequence_map_shortExact G N)
        (hF (Injective.under M) inferInstance)
        (F.mapShortComplex.map (injectiveCoefficientSequenceMap f))
        (G.mapShortComplex.map (injectiveCoefficientSequenceMap f))
      · exact coefficientDimensionShiftIso_δ _ _ _ _ _ _ _ _
      · exact coefficientDimensionShiftIso_δ _ _ _ _ _ _ _ _
      · exact e.hom.naturality (injectiveCoefficientSequenceMap f).τ₃)

/-- The one-step lift agrees with the given lower comparison on the actual
connecting map of the chosen injective short exact sequence. -/
@[reassoc]
lemma injectiveCoefficientHomologyStep_δ (n : ℕ)
    (hF : ∀ J : C, Injective J → IsZero ((F.obj J).homology (n + 1)))
    (hG : ∀ J : C, Injective J → IsZero ((G.obj J).homology (n + 1)))
    (e : F ⋙ homologyFunctor D (.up ℕ) n ≅ G ⋙ homologyFunctor D (.up ℕ) n)
    (M : C) :
    (injectiveCoefficientSequence_map_shortExact F M).δ n (n + 1) rfl ≫
        ((injectiveCoefficientHomologyStep F G n hF hG e).app M).hom =
      (e.app (cokernel (Injective.ι M))).hom ≫
        (injectiveCoefficientSequence_map_shortExact G M).δ n (n + 1) rfl :=
  coefficientDimensionShiftIso_δ
    (injectiveCoefficientSequence_map_shortExact F M) n
    (injectiveCoefficientSequence_map_shortExact G M)
    (hF (Injective.under M) inferInstance) (hG (Injective.under M) inferInstance)
    (e.app (Injective.under M)) (e.app (cokernel (Injective.ι M)))
    (e.hom.naturality (cokernel.π (Injective.ι M)))

/-- Positive injective acyclicity and a natural zero-degree comparison determine
natural homology isomorphisms in every degree. -/
def injectiveCoefficientHomologyNatIso
    (hF : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((F.obj J).homology n))
    (hG : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((G.obj J).homology n))
    (e₀ : F ⋙ homologyFunctor D (.up ℕ) 0 ≅ G ⋙ homologyFunctor D (.up ℕ) 0) :
    ∀ n : ℕ, F ⋙ homologyFunctor D (.up ℕ) n ≅ G ⋙ homologyFunctor D (.up ℕ) n
  | 0 => e₀
  | n + 1 => injectiveCoefficientHomologyStep F G n
      (fun J hJ => hF J hJ (n + 1) (Nat.zero_lt_succ n))
      (fun J hJ => hG J hJ (n + 1) (Nat.zero_lt_succ n))
      (injectiveCoefficientHomologyNatIso hF hG e₀ n)

/-- The recursive comparison recovers the prescribed zero-degree comparison. -/
@[simp]
lemma injectiveCoefficientHomologyNatIso_zero
    (hF : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((F.obj J).homology n))
    (hG : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((G.obj J).homology n))
    (e₀ : F ⋙ homologyFunctor D (.up ℕ) 0 ≅ G ⋙ homologyFunctor D (.up ℕ) 0) :
    injectiveCoefficientHomologyNatIso F G hF hG e₀ 0 = e₀ := rfl

/-- The recursive comparison is compatible with dimension shifting at every step. -/
@[reassoc]
lemma injectiveCoefficientHomologyNatIso_δ
    (hF : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((F.obj J).homology n))
    (hG : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((G.obj J).homology n))
    (e₀ : F ⋙ homologyFunctor D (.up ℕ) 0 ≅ G ⋙ homologyFunctor D (.up ℕ) 0)
    (n : ℕ) (M : C) :
    (injectiveCoefficientSequence_map_shortExact F M).δ n (n + 1) rfl ≫
        ((injectiveCoefficientHomologyNatIso F G hF hG e₀ (n + 1)).app M).hom =
      ((injectiveCoefficientHomologyNatIso F G hF hG e₀ n).app
        (cokernel (Injective.ι M))).hom ≫
        (injectiveCoefficientSequence_map_shortExact G M).δ n (n + 1) rfl :=
  injectiveCoefficientHomologyStep_δ F G n _ _ _ M

/-- Any family with the same degree-zero map and the same connecting-map
compatibility is equal to the recursive comparison. -/
lemma injectiveCoefficientHomologyNatIso_unique
    (hF : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((F.obj J).homology n))
    (hG : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((G.obj J).homology n))
    (e₀ : F ⋙ homologyFunctor D (.up ℕ) 0 ≅ G ⋙ homologyFunctor D (.up ℕ) 0)
    (α : ∀ n : ℕ, F ⋙ homologyFunctor D (.up ℕ) n ⟶ G ⋙ homologyFunctor D (.up ℕ) n)
    (h₀ : α 0 = e₀.hom)
    (hδ : ∀ n M,
      (injectiveCoefficientSequence_map_shortExact F M).δ n (n + 1) rfl ≫ (α (n + 1)).app M =
        (α n).app (cokernel (Injective.ι M)) ≫
          (injectiveCoefficientSequence_map_shortExact G M).δ n (n + 1) rfl) :
    ∀ n, α n = (injectiveCoefficientHomologyNatIso F G hF hG e₀ n).hom := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    apply NatTrans.ext
    funext M
    apply coefficientDimensionShift_unique
      (injectiveCoefficientSequence_map_shortExact F M) n
      (hF (Injective.under M) inferInstance (n + 1) (Nat.zero_lt_succ n))
    rw [hδ, ih]
    exact (injectiveCoefficientHomologyNatIso_δ F G hF hG e₀ n M).symm

end SerrePositivity
