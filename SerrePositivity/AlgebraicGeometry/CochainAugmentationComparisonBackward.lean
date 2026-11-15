module

public import SerrePositivity.AlgebraicGeometry.CechRefinementCone
public import SerrePositivity.AlgebraicGeometry.CochainComplexOfExactnessReflection

/-!
概要：比較の cone の完全性から、増大写像を含む微分の完全性を反映する。
方針：増大項の前像を取り、正次数では境界の反映を cone の完全性から得る。
規約：元の複体・増大写像・実際の比較写像を保持する。
使われ方：共通細分での既存の増大 cone の完全性の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- 完全な比較の cone と増大項の全単射は、増大列の完全性を反映する。 -/
theorem cochainAugmentation_exact_reflected_of_comparison
    (C D : CochainComplex (ModuleCat.{u} R) ℕ) (k : C ⟶ D)
    (Z Z' : ModuleCat.{u} R) (a : Z →ₗ[R] C.X 0) (a' : Z' →ₗ[R] D.X 0)
    (ζ : Z →ₗ[R] Z') (hζ : Function.Bijective ζ)
    (haug : (k.f 0).hom.comp a = a'.comp ζ)
    (hcycle : ∀ z, (C.d 0 1).hom (a z) = 0)
    (hk : (cechRefinementCone C D k).Acyclic)
    (hi : Function.Injective a') (he : Function.Exact a' (D.d 0 1).hom)
    (hd : ∀ n, Function.Exact (D.d n (n + 1)).hom (D.d (n + 1) (n + 2)).hom) :
    Function.Injective a ∧ Function.Exact a (C.d 0 1).hom ∧
      ∀ n, Function.Exact (C.d n (n + 1)).hom (C.d (n + 1) (n + 2)).hom := by
  have hdd : ∀ n, ModuleCat.ofHom (cechRefinementConeDifferential C D k n) ≫
      ModuleCat.ofHom (cechRefinementConeDifferential C D k (n + 1)) = 0 := by
    intro n
    apply ModuleCat.hom_ext
    exact cechRefinementConeDifferential_squared C D k n
  obtain ⟨hki, hke⟩ := cochainComplexOf_injective_exact_of_acyclic
    (cechRefinementConeTerm C D)
    (fun n ↦ ModuleCat.ofHom (cechRefinementConeDifferential C D k n)) hdd hk
  change Function.Injective (cechRefinementConeDifferential C D k 0) at hki
  change ∀ n, Function.Exact (cechRefinementConeDifferential C D k n)
    (cechRefinementConeDifferential C D k (n + 1)) at hke
  have hnat (n : ℕ) (x : C.X n) :
      (D.d n (n + 1)).hom ((k.f n).hom x) =
        (k.f (n + 1)).hom ((C.d n (n + 1)).hom x) :=
    congrArg (fun m ↦ m.hom x) (k.comm n (n + 1))
  have haugx (z : Z) : (k.f 0).hom (a z) = a' (ζ z) :=
    LinearMap.congr_fun haug z
  refine ⟨?_, ?_, ?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    apply (injective_iff_map_eq_zero _).mp hζ.1
    apply (injective_iff_map_eq_zero _).mp hi
    rw [← haugx, hz, map_zero]
  · intro x
    constructor
    · intro hx
      have hcx : (D.d 0 1).hom ((k.f 0).hom x) = 0 := by
        rw [hnat, hx, map_zero]
      obtain ⟨z', hz'⟩ := (he _).mp hcx
      obtain ⟨z, hz⟩ := hζ.2 z'
      have hr : x - a z = 0 := (injective_iff_map_eq_zero _).mp hki _ (by
        change ((k.f 0).hom (x - a z), -((C.d 0 1).hom (x - a z))) = (0, 0)
        rw [map_sub, haugx, hz, hz', sub_self, map_sub, hx, hcycle,
          sub_self, neg_zero])
      exact ⟨z, (sub_eq_zero.mp hr).symm⟩
    · rintro ⟨z, rfl⟩
      exact hcycle z
  · intro n x
    constructor
    · intro hx
      have hcx : (D.d (n + 1) (n + 2)).hom ((k.f (n + 1)).hom x) = 0 := by
        rw [hnat, hx, map_zero]
      obtain ⟨b, hb⟩ := (hd n _).mp hcx
      have hc : cechRefinementConeDifferential C D k (n + 1) (-b, x) = 0 := by
        change ((D.d n (n + 1)).hom (-b) + (k.f (n + 1)).hom x,
          -((C.d (n + 1) (n + 2)).hom x)) = (0, 0)
        rw [map_neg, hb, neg_add_cancel, hx, neg_zero]
      obtain ⟨y, hy⟩ := (hke n _).mp hc
      cases n with
      | zero =>
        change ((k.f 0).hom y, -((C.d 0 1).hom y)) = (-b, x) at hy
        refine ⟨-y, ?_⟩
        rw [map_neg]
        exact congrArg (fun w : D.X 0 × C.X 1 ↦ w.2) hy
      | succ n =>
        change ((D.d n (n + 1)).hom y.1 + (k.f (n + 1)).hom y.2,
          -((C.d (n + 1) (n + 2)).hom y.2)) = (-b, x) at hy
        refine ⟨-y.2, ?_⟩
        rw [map_neg]
        exact congrArg (fun w : D.X (n + 1) × C.X (n + 2) ↦ w.2) hy
    · rintro ⟨z, rfl⟩
      exact congrArg (fun m ↦ m.hom z) (C.d_comp_d n (n + 1) (n + 2))

end SerrePositivity.AlgebraicGeometry
