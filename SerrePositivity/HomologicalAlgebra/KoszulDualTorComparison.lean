module
public import SerrePositivity.HomologicalAlgebra.NonnegativeCochainHomology
public import SerrePositivity.HomologicalAlgebra.KoszulLinearDualityNaturality
public import SerrePositivity.HomologicalAlgebra.KoszulExtComparison

/-! # Natural comparison from nonnegative dual Koszul cohomology to complementary Tor -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The integer dual of a nonpositive complex has no negative terms. -/
lemma cochainLinearDual_isZero_X_of_neg (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) (M : ModuleCat.{u} R)
    (i : ℤ) (hi : i < 0) : IsZero (((cochainLinearDualFunctor K).obj M).X i) := by
  have : Subsingleton (((cochainLinearDualFunctor K).obj M).X i) :=
    ⟨fun f g => (hK (0 - i) (by omega)).eq_of_src f g⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Ext's nonnegative dual and the integer dual compute naturally the same homology. -/
def cochainLinearDualNonnegativeHomologyNatIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) (n : ℕ) :
    chainLinearYonedaFunctor (toChain K) ⋙ homologyFunctor (ModuleCat R) (.up ℕ) n ≅
      cochainLinearDualFunctor K ⋙ homologyFunctor (ModuleCat R) (.up ℤ) (n : ℤ) :=
  Functor.isoWhiskerRight (cochainLinearDualNonnegativeNatIso K).symm
      (homologyFunctor (ModuleCat R) (.up ℕ) n) ≪≫
    NatIso.ofComponents (fun M => nonnegativeCochainHomologyIso
      ((cochainLinearDualFunctor K).obj M) (cochainLinearDual_isZero_X_of_neg K hK M) n)
      (fun f => nonnegativeCochainHomologyIso_hom_naturality
        ((cochainLinearDualFunctor K).map f) _ _ n)

/-- Complementary Tor computes the actual dual Koszul cohomology, naturally in coefficients. -/
def koszulDualTorComparison {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z)
    (i : ℕ) (hi : i ≤ e) :
    koszulDualModuleFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
      (Tor (ModuleCat.{u} R) (e - i)).flip.obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) :=
  cochainLinearDualNonnegativeHomologyNatIso (koszulComplex z)
      (koszulComplex_isZero_X_of_pos z) i ≪≫
    koszulLinearDualHomologyNatIso z (i : ℤ) ≪≫
    Functor.isoWhiskerLeft (koszulModuleFunctor z)
      (eqToIso (congrArg (fun j : ℤ => homologyFunctor (ModuleCat.{u} R) (.up ℤ) j)
        (show (i : ℤ) - (e : ℤ) = -((e - i : ℕ) : ℤ) by omega))) ≪≫
    (koszulModuleTorComparison z hz (e - i)).symm

/-- Naturality reflects coefficient zero maps through the complementary Tor comparison. -/
lemma koszulDualTorComparison_map_eq_zero_iff {e : ℕ} (z : Fin e → R)
    (hz : IsKoszulResolution z) (i : ℕ) (hi : i ≤ e)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Tor (ModuleCat.{u} R) (e - i)).flip.obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range z)))).map f = 0 ↔
      homologyMap ((koszulDualModuleFunctor z).map f) i = 0 := by
  let E := koszulDualTorComparison z hz i hi
  have h := E.hom.naturality f
  change homologyMap ((koszulDualModuleFunctor z).map f) i ≫ E.hom.app N =
    E.hom.app M ≫ ((Tor (ModuleCat.{u} R) (e - i)).flip.obj
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range z)))).map f at h
  constructor
  · intro hf
    apply (cancel_mono (E.hom.app N)).mp
    rw [h, hf, comp_zero, zero_comp]
  · intro hf
    apply (cancel_epi (E.hom.app M)).mp
    rw [← h, hf, zero_comp, comp_zero]

/-- Higher Tor zero actions yield low-degree dual Koszul zero actions for actual multiplication. -/
lemma koszulDualHomology_coefficient_scalar_eq_zero_of_tor_annihilated
    {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z)
    (C : Type u) [CommRing C] [Algebra R C] (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : i < e) (c : C) (hc : c ∈ I) :
    homologyMap ((koszulDualModuleFunctor z).map
      (ModuleCat.ofHom (LinearMap.mulLeft R c))) i = 0 :=
  (koszulDualTorComparison_map_eq_zero_iff z hz i (Nat.le_of_lt hi)
    (ModuleCat.ofHom (LinearMap.mulLeft R c))).mp
      (hTor _ (e - i) (Nat.sub_pos_of_lt hi) c hc)

end SerrePositivity
