module
public import SerrePositivity.KTheory.DevissageFiltration

/-! # Restricting short exact sequences to a submodule and its quotient -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {M₁ M₂ M₃ : ModuleCat.{u} R}
  [Module.Finite R M₁] [Module.Finite R M₂] [Module.Finite R M₃]

/-- A finite module regarded as supported on the whole spectrum. -/
abbrev wholeSupportedModule (M : ModuleCat.{u} R) [Module.Finite R M] :
    SupportedFGModuleOn (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R)) :=
  ⟨M, inferInstance, Set.subset_univ _⟩

/-- The induced short exact sequence on the inverse image and image of a submodule. -/
def submoduleRestrictionShortExact (U : Submodule R M₂)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (he : Function.Exact f g) :
    SupportedModuleShortExact (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R)) := by
  let F : U.comap f →ₗ[R] U := f.restrict (fun _ h => h)
  let G : U →ₗ[R] U.map g := g.restrict (fun _ h => Submodule.mem_map_of_mem h)
  refine
    { left := wholeSupportedModule (ModuleCat.of R (U.comap f))
      middle := wholeSupportedModule (ModuleCat.of R U)
      right := wholeSupportedModule (ModuleCat.of R (U.map g))
      f := F
      g := G
      injective := fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
      exact := ?_
      surjective := ?_ }
  · intro n
    constructor
    · intro hn
      have hn' : g (n : M₂) = 0 := congrArg Subtype.val hn
      obtain ⟨m, hm⟩ := (he (n : M₂)).mp hn'
      exact ⟨⟨m, by change f m ∈ U; rw [hm]; exact n.property⟩, Subtype.ext hm⟩
    · rintro ⟨m, rfl⟩
      apply Subtype.ext
      exact he.apply_apply_eq_zero m
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm, hem⟩ := Submodule.mem_map.mp hn
    exact ⟨⟨m, hm⟩, Subtype.ext hem⟩

/-- The map on left quotients induced by the injective map. -/
def quotientRestrictionLeft (U : Submodule R M₂) (f : M₁ →ₗ[R] M₂) :
    (M₁ ⧸ U.comap f) →ₗ[R] (M₂ ⧸ U) := (U.comap f).mapQ U f le_rfl

/-- The map on right quotients induced by the surjective map. -/
def quotientRestrictionRight (U : Submodule R M₂) (g : M₂ →ₗ[R] M₃) :
    (M₂ ⧸ U) →ₗ[R] (M₃ ⧸ U.map g) := U.mapQ (U.map g) g
      (fun _ h => Submodule.mem_map_of_mem h)

omit [IsNoetherianRing R] [Module.Finite R M₁] [Module.Finite R M₂] in
lemma quotientRestrictionLeft_injective (U : Submodule R M₂) (f : M₁ →ₗ[R] M₂) :
    Function.Injective (quotientRestrictionLeft U f) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨m, rfl⟩ := (U.comap f).mkQ_surjective x
  have hm : f m ∈ U := (Submodule.Quotient.mk_eq_zero _).mp hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr hm

omit [IsNoetherianRing R] [Module.Finite R M₂] [Module.Finite R M₃] in
lemma quotientRestrictionRight_surjective (U : Submodule R M₂) (g : M₂ →ₗ[R] M₃)
    (hg : Function.Surjective g) : Function.Surjective (quotientRestrictionRight U g) := by
  intro x
  obtain ⟨m, rfl⟩ := (U.map g).mkQ_surjective x
  obtain ⟨n, rfl⟩ := hg m
  exact ⟨U.mkQ n, rfl⟩

omit [IsNoetherianRing R] [Module.Finite R M₁] [Module.Finite R M₂]
  [Module.Finite R M₃] in
lemma quotientRestriction_exact (U : Submodule R M₂)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (he : Function.Exact f g) :
    Function.Exact (quotientRestrictionLeft U f) (quotientRestrictionRight U g) := by
  intro x
  obtain ⟨m, rfl⟩ := U.mkQ_surjective x
  constructor
  · intro hx
    have hm : g m ∈ U.map g := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨v, hv, hvm⟩ := Submodule.mem_map.mp hm
    have hk : g (m - v) = 0 := by rw [map_sub, hvm, sub_self]
    obtain ⟨w, hw⟩ := (he (m - v)).mp hk
    refine ⟨(U.comap f).mkQ w, ?_⟩
    change U.mkQ (f w) = U.mkQ m
    have hv0 : U.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hw, map_sub, hv0, sub_zero]
  · rintro ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := (U.comap f).mkQ_surjective w
    rw [← hw]
    change (U.map g).mkQ (g (f v)) = 0
    rw [he.apply_apply_eq_zero v, map_zero]

/-- The short exact sequence on quotients by the inverse image and image of U. -/
def quotientRestrictionShortExact (U : Submodule R M₂)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (he : Function.Exact f g) (hg : Function.Surjective g) :
    SupportedModuleShortExact (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R)) where
  left := wholeSupportedModule (ModuleCat.of R (M₁ ⧸ U.comap f))
  middle := wholeSupportedModule (ModuleCat.of R (M₂ ⧸ U))
  right := wholeSupportedModule (ModuleCat.of R (M₃ ⧸ U.map g))
  f := quotientRestrictionLeft U f
  g := quotientRestrictionRight U g
  injective := quotientRestrictionLeft_injective U f
  exact := quotientRestriction_exact U f g he
  surjective := quotientRestrictionRight_surjective U g hg

omit [IsNoetherianRing R] [Module.Finite R M₁] [Module.Finite R M₂] in
/-- An annihilator bound passes backwards along an injective linear map. -/
lemma annihilator_le_of_injective (J : Ideal R) (f : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) (h : J ≤ Module.annihilator R M₂) :
    J ≤ Module.annihilator R M₁ :=
  h.trans (f.annihilator_le_of_injective hf)

omit [IsNoetherianRing R] [Module.Finite R M₂] [Module.Finite R M₃] in
/-- An annihilator bound passes forwards along a surjective linear map. -/
lemma annihilator_le_of_surjective (J : Ideal R) (g : M₂ →ₗ[R] M₃)
    (hg : Function.Surjective g) (h : J ≤ Module.annihilator R M₂) :
    J ≤ Module.annihilator R M₃ :=
  h.trans (g.annihilator_le_of_surjective hg)

/-- Restrict a filtration on the middle of a short exact sequence to both ends.
The sum of quotient-ring classes is additive for the resulting filtrations. -/
lemma DevissageFlag.exists_restriction {J : Ideal R} {M : ModuleCat.{u} R}
    (F : DevissageFlag J M) :
    ∀ [Module.Finite R M] {L N : ModuleCat.{u} R} [Module.Finite R L] [Module.Finite R N]
      (f : L →ₗ[R] M) (g : M →ₗ[R] N),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      ∃ (FL : DevissageFlag J L) (FN : DevissageFlag J N),
        F.value = FL.value + FN.value := by
  induction F with
  | @zero M hz =>
    intro _ L N _ _ f g hf he hg
    have : Subsingleton M := ModuleCat.subsingleton_of_isZero hz
    have hL : Subsingleton L := hf.subsingleton
    have hN : Subsingleton N := hg.subsingleton
    exact ⟨.zero (by have := hL; exact ModuleCat.isZero_of_subsingleton L),
      .zero (by have := hN; exact ModuleCat.isZero_of_subsingleton N), by simp [value]⟩
  | @step M U h rest ih =>
    intro _ L N _ _ f g hf he hg
    let E := submoduleRestrictionShortExact U f g hf he
    have hLfin : Module.Finite R E.left.obj := E.left.property.1
    have hNfin : Module.Finite R E.right.obj := E.right.property.1
    obtain ⟨FL, FN, hsum⟩ := ih E.f E.g E.injective E.exact E.surjective
    let Q := quotientRestrictionShortExact U f g he hg
    have hQ : J ≤ Module.annihilator R Q.middle.obj := h
    have hQL := annihilator_le_of_injective J Q.f Q.injective hQ
    have hQN := annihilator_le_of_surjective J Q.g Q.surjective hQ
    let GL : DevissageFlag J L := .step (U.comap f) hQL FL
    let GN : DevissageFlag J N := .step (U.map g) hQN FN
    refine ⟨GL, GN, ?_⟩
    have ha := annihilatedClass_shortExact J Q hQL hQ hQN
    change rest.value + annihilatedClass J (ModuleCat.of R (M ⧸ U)) h =
      (FL.value + annihilatedClass J Q.left.obj hQL) +
        (FN.value + annihilatedClass J Q.right.obj hQN)
    change annihilatedClass J (ModuleCat.of R (M ⧸ U)) h = _ at ha
    rw [hsum, ha]
    abel

end SerrePositivity
