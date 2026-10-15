module
public import SerrePositivity.HomologicalAlgebra.KoszulTorComparison
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Coefficient ideals acting trivially on actual Tor objects -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- Tor is additive in its coefficient variable as an actual functor. -/
instance torFixedRight_additive (N : ModuleCat.{u} R) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).flip.obj N).Additive where
  map_add {X Y f g} := by
    simp only [Functor.flip_obj_map, Tor_map, CategoryTheory.Functor.map_add,
      NatTrans.leftDerived, NatTrans.leftDerivedToHomotopyCategory,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.mapHomotopyCategory_app]
    rw [← CategoryTheory.Functor.map_add, ← CategoryTheory.Functor.map_add]
    congr 2
    ext j
    simp [tensoringLeft]

/-- Coefficient scalars killed by an additive functor form an ideal. -/
def coefficientFunctorAnnihilator (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] :
    Ideal C where
  carrier := {c | F.map (ModuleCat.ofHom (LinearMap.mulLeft R c)) = 0}
  zero_mem' := by
    have h : ModuleCat.ofHom (LinearMap.mulLeft R (0 : C)) =
        (0 : ModuleCat.of R C ⟶ ModuleCat.of R C) := by ext x; simp
    simp only [Set.mem_ofPred_eq, h, Functor.map_zero]
  add_mem' := by
    intro a b ha hb
    change F.map (ModuleCat.ofHom (LinearMap.mulLeft R (a + b))) = 0
    have h : ModuleCat.ofHom (LinearMap.mulLeft R (a + b)) =
        ModuleCat.ofHom (LinearMap.mulLeft R a) +
          ModuleCat.ofHom (LinearMap.mulLeft R b) := by ext x; simp [add_mul]
    rw [h, Functor.map_add, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    change F.map (ModuleCat.ofHom (LinearMap.mulLeft R (c * a))) = 0
    have h : ModuleCat.ofHom (LinearMap.mulLeft R (c * a)) =
        ModuleCat.ofHom (LinearMap.mulLeft R a) ≫
          ModuleCat.ofHom (LinearMap.mulLeft R c) := by ext x; simp
    rw [h, Functor.map_comp, ha, zero_comp]

/-- Zero action on ideal generators implies zero action on the full image ideal. -/
lemma coefficientFunctor_mapIdeal_eq_zero
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]
    {S : Type u} [CommRing S] (φ : S →+* C) (I : Ideal S)
    (hI : ∀ s ∈ I, F.map (ModuleCat.ofHom (LinearMap.mulLeft R (φ s))) = 0) :
    ∀ c ∈ I.map φ, F.map (ModuleCat.ofHom (LinearMap.mulLeft R c)) = 0 := by
  have h : I.map φ ≤ coefficientFunctorAnnihilator (C := C) F :=
    Ideal.map_le_iff_le_comap.mpr hI
  exact h

/-- The concrete first-variable Tor action vanishes on the entire coefficient image ideal. -/
lemma torCoefficientScalarEndomorphism_mapIdeal_eq_zero
    {S : Type u} [CommRing S] (φ : S →+* C) (I : Ideal S)
    (N : ModuleCat.{u} R) (i : ℕ)
    (hI : ∀ s ∈ I, torCoefficientScalarEndomorphism C N i (φ s) = 0) :
    ∀ c ∈ I.map φ, torCoefficientScalarEndomorphism C N i c = 0 :=
  coefficientFunctor_mapIdeal_eq_zero ((Tor (ModuleCat.{u} R) i).flip.obj N) φ I hI

end SerrePositivity
