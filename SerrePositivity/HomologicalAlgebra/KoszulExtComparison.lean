module
public import SerrePositivity.HomologicalAlgebra.ProjectiveExtNaturality
public import SerrePositivity.HomologicalAlgebra.ResolutionNaturality
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyKoszulPowers
public import SerrePositivity.CommutativeAlgebra.Koszul.Powers

/-! # Canonically augmented Koszul resolutions and natural Ext comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex DerivedCompletion
variable {R : Type u} [CommRing R]

/-- Use the standard quotient normalization on the zero-th Koszul homology. -/
def canonicalIsResolutionOfKoszul {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z) :
    IsResolutionOf (koszulComplex z) (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) where
  isZero_X := koszulComplex_isZero_X_of_pos z
  projective := koszulComplex_projective_X z
  isZero_homology := hz.isZero
  homologyZeroIso := (koszulCanonicalH0Equiv R z).toModuleIso

/-- The Koszul projective resolution with the actual standard quotient augmentation. -/
def canonicalKoszulResolution {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) :=
  (canonicalIsResolutionOfKoszul z hz).toProjectiveResolution

/-- The dual Koszul cochain complex as a functor of arbitrary coefficient modules. -/
abbrev koszulDualModuleFunctor {e : ℕ} (z : Fin e → R) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  chainLinearYonedaFunctor (toChain (koszulComplex z))

/-- Ext is naturally computed by the standard augmented dual Koszul complex. -/
def koszulExtComparison {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z) (i : ℕ) :
    (Ext R (ModuleCat R) i).obj (op (ModuleCat.of R (R ⧸ Ideal.span (Set.range z)))) ≅
      koszulDualModuleFunctor z ⋙ homologyFunctor (ModuleCat R) (.up ℕ) i :=
  projectiveResolutionExtNatIso (canonicalKoszulResolution z hz) i

/-- A list consisting of units equal to one is weakly regular, including on zero modules. -/
lemma isWeaklyRegular_replicate_one (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular M (List.replicate n (1 : R)) := by
  induction n generalizing M with
  | zero => exact .nil R M
  | succ n ih =>
    rw [List.replicate_succ]
    apply RingTheory.Sequence.IsWeaklyRegular.cons
    · intro x y h
      simpa only [one_smul] using h
    · exact ih _

/-- The power-zero Koszul complex is a resolution as well; no proper-ideal condition is added. -/
lemma isKoszulResolution_power_zero {e : ℕ} (z : Fin e → R) :
    IsKoszulResolution (fun j => z j ^ (0 : ℕ)) := by
  apply isKoszulResolution_of_isWeaklyRegular
  simpa only [pow_zero, List.ofFn_const] using
    isWeaklyRegular_replicate_one (R := R) R e

/-- Supply all power resolutions, including the zero-th stage of the actual ideal diagram. -/
lemma isKoszulResolution_all_powers [IsLocalRing R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z)) (n : ℕ) :
    IsKoszulResolution (fun j => z j ^ n) := by
  cases n with
  | zero => exact isKoszulResolution_power_zero z
  | succ n => exact isKoszulResolution_powers_of_isWeaklyRegular z hz hreg (n + 1) (by omega)

/-- The real dual Koszul transition has the direction required by the Ext direct system. -/
def koszulDualPowerTransition {e : ℕ} (z : Fin e → R) (n : ℕ) :
    koszulDualModuleFunctor (fun j => z j ^ n) ⟶
      koszulDualModuleFunctor (fun j => z j ^ (n + 1)) :=
  chainLinearYonedaMap (restrictionMap (powerKoszulTransition R z n) embUp)

/-- Standard quotient normalization makes the power transition an augmented resolution map. -/
lemma canonicalKoszulResolution_power_transition {e : ℕ} (z : Fin e → R) (n : ℕ)
    (h₀ : IsKoszulResolution (fun j => z j ^ n))
    (h₁ : IsKoszulResolution (fun j => z j ^ (n + 1))) :
    (restrictionMap (powerKoszulTransition R z n) embUp).f 0 ≫
        (canonicalKoszulResolution _ h₀).π.f 0 =
      (canonicalKoszulResolution _ h₁).π.f 0 ≫
        (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
          (homOfLE (Nat.le_succ n)).op := by
  apply (canonicalIsResolutionOfKoszul _ h₁).restrictionMap_π_f_zero
    (canonicalIsResolutionOfKoszul _ h₀) (powerKoszulTransition R z n)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact powerKoszulStageH0Equiv_transition R z n x

/-- Ext's standard quotient arrows agree with the actual dual Koszul transitions. -/
lemma koszulExtComparison_power_transition {e : ℕ} (z : Fin e → R) (n i : ℕ)
    (h₀ : IsKoszulResolution (fun j => z j ^ n))
    (h₁ : IsKoszulResolution (fun j => z j ^ (n + 1))) :
    (Ext R (ModuleCat R) i).map
        ((localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
          (homOfLE (Nat.le_succ n)).op).op ≫ (koszulExtComparison _ h₁ i).hom =
      (koszulExtComparison _ h₀ i).hom ≫
        Functor.whiskerRight (koszulDualPowerTransition z n)
          (homologyFunctor (ModuleCat R) (.up ℕ) i) := by
  apply NatTrans.ext
  funext M
  exact projectiveResolutionIsoExt_first_naturality _
    (canonicalKoszulResolution _ h₁) (canonicalKoszulResolution _ h₀)
    (restrictionMap (powerKoszulTransition R z n) embUp)
    (canonicalKoszulResolution_power_transition z n h₀ h₁) M i

/-- On the standard regular parameter sequence all power stages admit the natural comparison. -/
def koszulExtPowersComparison [IsLocalRing R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z)) (n i : ℕ) :
    (Ext R (ModuleCat R) i).obj (op (ModuleCat.of R (R ⧸ powerKoszulIdeal R z n))) ≅
      koszulDualModuleFunctor (fun j => z j ^ n) ⋙ homologyFunctor (ModuleCat R) (.up ℕ) i :=
  koszulExtComparison _ (isKoszulResolution_all_powers z hz hreg n) i

end SerrePositivity
