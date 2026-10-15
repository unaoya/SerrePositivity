module
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyKoszulComparison
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyAction

/-! # Coefficient actions and zero maps in the dual Koszul local-cohomology comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A map killed by every stage functor is killed by their actual sequential colimit. -/
lemma sequentialFunctorColimit_map_eq_zero
    (F : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R))
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (h : ∀ n, (F.obj n).map f = 0) : (colimit F).map f = 0 := by
  apply (isColimitOfPreserves ((evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj M)
    (colimit.isColimit F)).hom_ext
  intro n
  change (colimit.ι F n).app M ≫ (colimit F).map f = (colimit.ι F n).app M ≫ 0
  rw [← (colimit.ι F n).naturality f, h n, zero_comp, comp_zero]

/-- It suffices that stage maps vanish at arbitrarily large indices. -/
lemma sequentialFunctorColimit_map_eq_zero_of_cofinal_stages
    (F : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R))
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (h : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ (F.obj m).map f = 0) :
    (colimit F).map f = 0 := by
  apply (isColimitOfPreserves ((evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj M)
    (colimit.isColimit F)).hom_ext
  intro n
  obtain ⟨m, hnm, hm⟩ := h n
  have hw : (F.map (homOfLE hnm)).app M ≫ (colimit.ι F m).app M =
      (colimit.ι F n).app M :=
    congrArg (fun α => α.app M) (colimit.w F (homOfLE hnm))
  change (colimit.ι F n).app M ≫ (colimit F).map f = (colimit.ι F n).app M ≫ 0
  calc
    _ = (F.map (homOfLE hnm)).app M ≫ (colimit.ι F m).app M ≫ (colimit F).map f := by
      rw [← Category.assoc, hw]
    _ = 0 := by rw [← (colimit.ι F m).naturality f, hm, zero_comp, comp_zero]
    _ = _ := by rw [comp_zero]

/-- The actual complex-colimit comparison reflects zero maps in either direction. -/
lemma koszulLocalCohomology_map_eq_zero_iff [IsNoetherian R R]
    {e : ℕ} (z : Fin e → R)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (localCohomology (Ideal.span (Set.range z)) i).map f = 0 ↔
      homologyMap ((koszulDualColimitFunctor z).map f) i = 0 := by
  let E := koszulLocalCohomologyComparison z hres i
  have h := E.hom.naturality f
  change homologyMap ((koszulDualColimitFunctor z).map f) i ≫ E.hom.app N =
    E.hom.app M ≫ (localCohomology (Ideal.span (Set.range z)) i).map f at h
  constructor
  · intro hf
    apply (cancel_mono (E.hom.app N)).mp
    rw [h, hf, comp_zero, zero_comp]
  · intro hf
    apply (cancel_epi (E.hom.app M)).mp
    rw [← h, hf, zero_comp, comp_zero]

/-- Zero maps on every finite-stage dual Koszul cohomology give zero local-cohomology maps. -/
lemma koszulLocalCohomology_map_eq_zero_of_stages [IsNoetherian R R]
    {e : ℕ} (z : Fin e → R)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ)
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (h : ∀ n : ℕ, homologyMap
      ((koszulDualModuleFunctor (fun j => z j ^ n)).map f) i = 0) :
    (localCohomology (Ideal.span (Set.range z)) i).map f = 0 := by
  let E := koszulDualPowerHomologyColimitNatIso z hres i
  have hf : (colimit (koszulDualPowerHomologyDiagram z i)).map f = 0 :=
    sequentialFunctorColimit_map_eq_zero _ f h
  apply (cancel_epi (E.hom.app M)).mp
  rw [← E.hom.naturality f, hf, zero_comp, comp_zero]

/-- Positive power stages suffice; the power-zero stage needs no separate vanishing input. -/
lemma koszulLocalCohomology_map_eq_zero_of_positive_stages [IsNoetherian R R]
    {e : ℕ} (z : Fin e → R)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ)
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (h : ∀ n : ℕ, 0 < n → homologyMap
      ((koszulDualModuleFunctor (fun j => z j ^ n)).map f) i = 0) :
    (localCohomology (Ideal.span (Set.range z)) i).map f = 0 := by
  let E := koszulDualPowerHomologyColimitNatIso z hres i
  have hf : (colimit (koszulDualPowerHomologyDiagram z i)).map f = 0 := by
    apply sequentialFunctorColimit_map_eq_zero_of_cofinal_stages _ f
    intro n
    exact ⟨n + 1, Nat.le_succ n, h (n + 1) (Nat.zero_lt_succ n)⟩
  apply (cancel_epi (E.hom.app M)).mp
  rw [← E.hom.naturality f, hf, zero_comp, comp_zero]

variable {e : ℕ} (z : Fin e → R) (i : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]

/-- Actual coefficient multiplication on the homology of the dual Koszul complex colimit. -/
def koszulDualColimitScalarEndomorphism (c : C) :
    ((koszulDualColimitFunctor z).obj (ModuleCat.of R C)).homology i ⟶
      ((koszulDualColimitFunctor z).obj (ModuleCat.of R C)).homology i :=
  homologyMap ((koszulDualColimitFunctor z).map
    (ModuleCat.ofHom (LinearMap.mulLeft R c))) i

/-- The comparison intertwines actual coefficient multiplication with local cohomology. -/
lemma koszulLocalCohomologyComparison_coefficient_scalar [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (c : C) :
    koszulDualColimitScalarEndomorphism z i C c ≫
        (koszulLocalCohomologyComparison z hres i).hom.app (ModuleCat.of R C) =
      (koszulLocalCohomologyComparison z hres i).hom.app (ModuleCat.of R C) ≫
        HomologicalAlgebra.localCohomologyScalarEndomorphism
          (Ideal.span (Set.range z)) i C c :=
  (koszulLocalCohomologyComparison z hres i).hom.naturality
    (ModuleCat.ofHom (LinearMap.mulLeft R c))

/-- Scalar zero action is equivalent on the actual colimit and local-cohomology sides. -/
lemma koszulLocalCohomology_coefficient_scalar_eq_zero_iff [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (c : C) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
        (Ideal.span (Set.range z)) i C c = 0 ↔
      koszulDualColimitScalarEndomorphism z i C c = 0 :=
  koszulLocalCohomology_map_eq_zero_iff z hres i
    (ModuleCat.ofHom (LinearMap.mulLeft R c))

/-- Finite-stage coefficient zero actions descend to the concrete local-cohomology action. -/
lemma localCohomologyScalarEndomorphism_eq_zero_of_dualKoszul_stages
    [IsNoetherian R R] (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (c : C) (h : ∀ n : ℕ, homologyMap
      ((koszulDualModuleFunctor (fun j => z j ^ n)).map
        (ModuleCat.ofHom (LinearMap.mulLeft R c))) i = 0) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
      (Ideal.span (Set.range z)) i C c = 0 :=
  koszulLocalCohomology_map_eq_zero_of_stages z hres i
    (ModuleCat.ofHom (LinearMap.mulLeft R c)) h

end SerrePositivity
