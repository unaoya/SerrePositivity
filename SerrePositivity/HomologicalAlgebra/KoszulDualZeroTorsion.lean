module
public import SerrePositivity.HomologicalAlgebra.KoszulDualZeroTransitions
public import SerrePositivity.HomologicalAlgebra.IdealPowerTorsion
public import SerrePositivity.HomologicalAlgebra.KoszulDualCoefficientExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Zero dual Koszul cohomology computes actual ideal-power torsion -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite HomologicalComplex
open DerivedCompletion
variable {R : Type u} [CommRing R] [IsNoetherian R R] {e : ℕ} (z : Fin e → R)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- Evaluation at one gives a natural inclusion of each quotient-Hom stage into power torsion. -/
def powerKoszulQuotientHomToTorsion (n : ℕ) :
    (powerKoszulQuotientHomDiagram z).obj n ⟶
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) where
  app M := ModuleCat.ofHom
    { toFun := fun (f : ModuleCat.of R (R ⧸ powerKoszulIdeal R z n) ⟶ M) => ⟨f 1, by
        obtain ⟨k, hk⟩ := exists_span_pow_le_powerKoszulIdeal z n
        apply (Ideal.primaryComponent_mem _ _ _).mpr
        refine ⟨k, ?_⟩
        rw [Submodule.mem_torsionBySet_iff]
        intro a
        have hf := (quotientHomEvalOneEquiv (powerKoszulIdeal R z n) M f).property
        exact (Submodule.mem_torsionBySet_iff _ _).mp hf ⟨a, hk a.property⟩⟩
      map_add' := by intro f g; apply Subtype.ext; rfl
      map_smul' := by intro r f; apply Subtype.ext; rfl }
  naturality {M N} f := by ext g; rfl

/-- These natural evaluations respect the actual quotient transition maps. -/
def powerKoszulQuotientHomTorsionCocone : Cocone (powerKoszulQuotientHomDiagram z) where
  pt := idealPowerTorsionFunctor (Ideal.span (Set.range z))
  ι := NatTrans.ofSequence (powerKoszulQuotientHomToTorsion z) (by
    intro n
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl)

/-- The natural map from the actual quotient-Hom colimit to the actual power-torsion functor. -/
def quotientHomColimitToPowerTorsion :
    colimit (powerKoszulQuotientHomDiagram z) ⟶
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) :=
  colimit.desc _ (powerKoszulQuotientHomTorsionCocone z)

/-- Evaluation is injective at every actual quotient stage. -/
instance powerKoszulQuotientHomToTorsion_mono (n : ℕ) :
    Mono (powerKoszulQuotientHomToTorsion z n) := by
  have : ∀ M : ModuleCat.{u} R, Mono ((powerKoszulQuotientHomToTorsion z n).app M) := by
    intro M
    apply (ModuleCat.mono_iff_injective _).mpr
    intro f g h
    apply (quotientHomEvalOneEquiv (powerKoszulIdeal R z n) M).injective
    apply Subtype.ext
    change (f : ModuleCat.of R (R ⧸ powerKoszulIdeal R z n) ⟶ M).hom
        (1 : R ⧸ powerKoszulIdeal R z n) =
      (g : ModuleCat.of R (R ⧸ powerKoszulIdeal R z n) ⟶ M).hom
        (1 : R ⧸ powerKoszulIdeal R z n)
    exact congrArg Subtype.val h
  exact NatTrans.mono_of_mono_app _

/-- Exact filtered colimits retain injectivity of the map into the constant torsion functor. -/
instance quotientHomColimitToPowerTorsion_mono : Mono (quotientHomColimitToPowerTorsion z) := by
  have : IsConnected ℕ := IsFiltered.isConnected ℕ
  have : ∀ n, Mono ((powerKoszulQuotientHomTorsionCocone z).ι.app n) := fun n =>
    powerKoszulQuotientHomToTorsion_mono z n
  have := NatTrans.mono_of_mono_app (powerKoszulQuotientHomTorsionCocone z).ι
  exact colim.map_mono' (powerKoszulQuotientHomTorsionCocone z).ι
    (colimit.isColimit _) (isColimitConstCocone ℕ _)
    (quotientHomColimitToPowerTorsion z) (fun n => by simp [quotientHomColimitToPowerTorsion])

/-- Every ideal-power-torsion element is the evaluation of an actual quotient-Hom stage. -/
lemma quotientHomColimitToPowerTorsion_surjective (M : ModuleCat.{u} R) :
    Function.Surjective ((quotientHomColimitToPowerTorsion z).app M) := by
  intro x
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem _ _ _).mp x.property
  let y : Submodule.torsionBySet R M (powerKoszulIdeal R z n : Set R) := ⟨x.val, by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    exact (Submodule.mem_torsionBySet_iff _ _).mp hn
      ⟨a, powerKoszulIdeal_le_span_pow z n a.property⟩⟩
  let f := (quotientHomEvalOneEquiv (powerKoszulIdeal R z n) M).symm y
  refine ⟨(colimit.ι (powerKoszulQuotientHomDiagram z) n).app M f, ?_⟩
  have h := congrArg (fun α => α.app M)
    (colimit.ι_desc (powerKoszulQuotientHomTorsionCocone z) n)
  have hx := congrArg (fun g => g f) h
  apply Subtype.ext
  rw [show ((quotientHomColimitToPowerTorsion z).app M)
      ((colimit.ι (powerKoszulQuotientHomDiagram z) n).app M f) =
        (powerKoszulQuotientHomToTorsion z n).app M f from hx]
  change f 1 = x.val
  exact quotientHomEvalOneEquiv_symm_apply_one _ _ y

/-- The actual quotient-Hom colimit is precisely the actual ideal-power torsion functor. -/
def quotientHomColimitPowerTorsionNatIso :
    colimit (powerKoszulQuotientHomDiagram z) ≅
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) := by
  have : ∀ M : ModuleCat.{u} R, IsIso ((quotientHomColimitToPowerTorsion z).app M) := by
    intro M
    have : Epi ((quotientHomColimitToPowerTorsion z).app M) :=
      (ModuleCat.epi_iff_surjective _).mpr (quotientHomColimitToPowerTorsion_surjective z M)
    exact isIso_of_mono_of_epi _
  have := NatIso.isIso_of_isIso_app (quotientHomColimitToPowerTorsion z)
  exact asIso (quotientHomColimitToPowerTorsion z)

/-- The actual zero dual-colimit cohomology is actual power torsion, naturally in coefficients. -/
def koszulDualColimitZeroTorsionNatIso :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) :=
  koszulDualColimitZeroQuotientHomNatIso z ≪≫ quotientHomColimitPowerTorsionNatIso z

/-- Exact filtered colimits of the quotient-Hom functors make power torsion left exact. -/
lemma parameterPowerTorsionFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (idealPowerTorsionFunctor (Ideal.span (Set.range z))) := by
  have : ∀ n, PreservesFiniteLimits ((powerKoszulQuotientHomDiagram z).obj n) := by
    intro n
    change PreservesFiniteLimits ((linearCoyoneda R (ModuleCat.{u} R)).obj
      (op (ModuleCat.of R (R ⧸ powerKoszulIdeal R z n))))
    infer_instance
  exact preservesFiniteLimits_of_natIso (quotientHomColimitPowerTorsionNatIso z)

end SerrePositivity
