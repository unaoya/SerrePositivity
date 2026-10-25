module

public import SerrePositivity.BhattScholze.Delta.DeltaRing
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteSequenceSum
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure

/-! # δ基底像のFrobeniusに関する実導来完備性

W₂のねじれた作用に必要な、p,d完備からp,φ(d)完備への具体的接続。
既存の実導来完備性の漸化式判定を使い、古典的完備性には置き換えない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard

private theorem neumann_bijective (R : Type u) [CommRing R] (b : R)
    (M : ModuleCat.{u} R) (hb : IsModuleComplete R b M) (L : Module.End R M) :
    Function.Bijective (fun x : M ↦ x - b • L x) := by
  have hr := (isModuleComplete_iff_recurrence_bijective R b M).mp hb
  let Q : Module.End R M := LinearMap.id - b • L
  change Function.Bijective Q
  constructor
  · apply (injective_iff_map_eq_zero Q).mpr
    intro x hx
    have he : x = b • L x := sub_eq_zero.mp hx
    let z : ℕ → M := fun k ↦ (L ^ k) x
    have hz : adicRecurrenceMap b z = 0 := by
      funext k
      change (L ^ k) x - b • (L ^ (k + 1)) x = 0
      have h := congrArg (fun t ↦ (L ^ k) t) he
      rw [map_smul] at h
      rw [pow_succ, Module.End.mul_apply, h, sub_self]
    have hzero := hr.injective (hz.trans (map_zero _).symm)
    simpa [z] using congrFun hzero 0
  · intro y
    obtain ⟨z, hz⟩ := hr.surjective (fun k ↦ (L ^ k) y)
    have hshift : (fun k ↦ L (z k)) = fun k ↦ z (k + 1) := by
      apply hr.injective
      funext k
      change L (z k) - b • L (z (k + 1)) = z (k + 1) - b • z (k + 1 + 1)
      rw [← map_smul, ← map_sub]
      have h0 := congrFun hz k
      have h1 := congrFun hz (k + 1)
      change z k - b • z (k + 1) = (L ^ k) y at h0
      change z (k + 1) - b • z (k + 1 + 1) = (L ^ (k + 1)) y at h1
      rw [h0, h1, pow_succ', Module.End.mul_apply]
    refine ⟨z 0, ?_⟩
    change z 0 - b • L (z 0) = y
    rw [congrFun hshift 0]
    simpa [adicRecurrenceMap] using congrFun hz 0

private theorem complete_add (R : Type u) [CommRing R] (a b : R)
    (M : ModuleCat.{u} R) (ha : IsModuleComplete R a M) (hb : IsModuleComplete R b M) :
    IsModuleComplete R (a + b) M := by
  let P := ModuleCat.of R (ℕ → M)
  have hbP : IsModuleComplete R b P :=
    isModuleComplete_pi R b (fun _ : ℕ ↦ M) (fun _ ↦ hb)
  let E := adicRecurrenceEquiv R a M ha
  let shift : Module.End R P :=
    { toFun := fun x n ↦ x (n + 1)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let L : Module.End R P := E.symm.toLinearMap.comp shift
  have hL (x : P) : adicRecurrenceMap a (L x) = shift x := E.apply_symm_apply (shift x)
  have he (x : P) : adicRecurrenceMap (a + b) x = adicRecurrenceMap a (x - b • L x) := by
    rw [map_sub, map_smul, hL]
    funext n
    change x n - (a + b) • x (n + 1) = x n - a • x (n + 1) - b • x (n + 1)
    rw [add_smul]
    abel
  apply (isModuleComplete_iff_recurrence_bijective R (a + b) M).mpr
  have h := E.bijective.comp (neumann_bijective R b P hbP L)
  convert h using 1
  funext x
  exact he x

private theorem complete_of_power (R : Type u) [CommRing R] (f : R) (n : ℕ) (hn : n ≠ 0)
    (M : ModuleCat.{u} R) (h : IsModuleComplete R (f ^ n) M) : IsModuleComplete R f M := by
  let S := Localization.Away (f ^ n)
  have hu : IsUnit (algebraMap R S f) := (isUnit_pow_iff hn).mp (by
    rw [← map_pow]
    exact IsLocalization.Away.algebraMap_isUnit (f ^ n))
  have hle : Submonoid.powers (f ^ n) ≤ Submonoid.powers f :=
    Submonoid.powers_le.mpr ⟨n, rfl⟩
  let : IsLocalization (Submonoid.powers f) S :=
    IsLocalization.of_le (Submonoid.powers (f ^ n)) (Submonoid.powers f) hle (by
      rintro _ ⟨k, rfl⟩
      simpa only [map_pow] using hu.pow k)
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) S
  let E : localizationObject R f ≅ localizationObject R (f ^ n) :=
    (moduleObjectFunctor R).mapIso e.toLinearEquiv.toModuleIso
  change IsComplete R f ((moduleObjectFunctor R).obj M)
  change IsComplete R (f ^ n) ((moduleObjectFunctor R).obj M) at h
  intro q g
  apply (cancel_epi E.inv).mp
  simpa only [comp_zero] using h q (E.inv ≫ g)

/-- p,f(d)導来完備な終域はf(φ(d))導来完備。pねじれ・非Noether環を許す。 -/
theorem deltaImage_frobenius_isModuleComplete {p : ℕ} [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] (D : DeltaStructure p A) (f : A →+* B) (d : A)
    (hp : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hd : IsModuleComplete B (f d) (ModuleCat.of B B)) :
    IsModuleComplete B (f (D.frobeniusLift d)) (ModuleCat.of B B) := by
  have hpow : IsModuleComplete B (f d ^ p) (ModuleCat.of B B) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fact.out : p.Prime).ne_zero
    rw [hn, pow_succ']
    exact isModuleComplete_mul_right B (f d) (f d ^ n) _ hd
  have hmul := isModuleComplete_mul_right B (p : B) (f (D.delta d)) _ hp
  have h := complete_add B (f d ^ p) ((p : B) * f (D.delta d)) _ hpow hmul
  simpa only [D.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast] using h

/-- p,f(φ(d))導来完備ならf(d)導来完備。完備化で逆Frobeniusを延長するための逆向き。 -/
theorem deltaImage_isModuleComplete_of_frobenius {p : ℕ} [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] (D : DeltaStructure p A) (f : A →+* B) (d : A)
    (hp : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hd : IsModuleComplete B (f (D.frobeniusLift d)) (ModuleCat.of B B)) :
    IsModuleComplete B (f d) (ModuleCat.of B B) := by
  have hm := isModuleComplete_mul_right B (p : B) (-f (D.delta d)) _ hp
  have hs := complete_add B (f (D.frobeniusLift d)) ((p : B) * -f (D.delta d)) _ hd hm
  have he : f (D.frobeniusLift d) + (p : B) * -f (D.delta d) = f d ^ p := by
    rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast]
    ring
  rw [he] at hs
  exact complete_of_power B (f d) p (Fact.out : p.Prime).ne_zero _ hs

end SerrePositivity.BhattScholze
