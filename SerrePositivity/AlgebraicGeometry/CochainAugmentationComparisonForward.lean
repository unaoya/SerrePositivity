module

public import SerrePositivity.AlgebraicGeometry.CechRefinementCone
public import SerrePositivity.AlgebraicGeometry.CochainComplexOfExactnessReflection

/-!
概要：比較の cone の完全性から、増大写像を含む微分の完全性を正向きに移す。
方針：cone のサイクルを持ち上げ、零次では増大項の全単射性を使う。
規約：新しい増大複体を作らず、元の複体と実際の比較写像を保持する。
使われ方：共通細分での既存の増大 cone の完全性の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- 完全な比較の cone と増大項の全単射は、増大列の完全性を正向きに移す。 -/
theorem cochainAugmentation_exact_of_comparison
    (C D : CochainComplex (ModuleCat.{u} R) ℕ) (k : C ⟶ D)
    (Z Z' : ModuleCat.{u} R) (a : Z →ₗ[R] C.X 0) (a' : Z' →ₗ[R] D.X 0)
    (ζ : Z →ₗ[R] Z') (hζ : Function.Bijective ζ)
    (haug : (k.f 0).hom.comp a = a'.comp ζ)
    (hcycle' : ∀ z, (D.d 0 1).hom (a' z) = 0)
    (hk : (cechRefinementCone C D k).Acyclic)
    (hi : Function.Injective a) (he : Function.Exact a (C.d 0 1).hom)
    (hd : ∀ n, Function.Exact (C.d n (n + 1)).hom (C.d (n + 1) (n + 2)).hom) :
    Function.Injective a' ∧ Function.Exact a' (D.d 0 1).hom ∧
      ∀ n, Function.Exact (D.d n (n + 1)).hom (D.d (n + 1) (n + 2)).hom := by
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
    intro z' hz'
    obtain ⟨z, rfl⟩ := hζ.2 z'
    have haz : a z = 0 := (injective_iff_map_eq_zero _).mp hki _ (by
      change ((k.f 0).hom (a z), -((C.d 0 1).hom (a z))) = (0, 0)
      rw [haugx, hz', (he _).mpr ⟨z, rfl⟩, neg_zero])
    have hz : z = 0 := (injective_iff_map_eq_zero _).mp hi z haz
    rw [hz, map_zero]
  · intro y
    constructor
    · intro hy
      have hc : cechRefinementConeDifferential C D k 1 (y, 0) = 0 := by
        change ((D.d 0 1).hom y + (k.f 1).hom 0, -(C.d 1 2).hom 0) = (0, 0)
        rw [hy, map_zero, map_zero, neg_zero, add_zero]
      obtain ⟨x, hx⟩ := (hke 0 _).mp hc
      change ((k.f 0).hom x, -((C.d 0 1).hom x)) = (y, 0) at hx
      have hcx : (C.d 0 1).hom x = 0 := neg_eq_zero.mp
        (congrArg (fun w : D.X 0 × C.X 1 ↦ w.2) hx)
      obtain ⟨z, hz⟩ := (he x).mp hcx
      refine ⟨ζ z, ?_⟩
      rw [← haugx, hz]
      exact congrArg (fun w : D.X 0 × C.X 1 ↦ w.1) hx
    · rintro ⟨z, rfl⟩
      exact hcycle' z
  · intro n y
    constructor
    · intro hy
      have hc : cechRefinementConeDifferential C D k (n + 2) (y, 0) = 0 := by
        change ((D.d (n + 1) (n + 2)).hom y + (k.f (n + 2)).hom 0,
          -(C.d (n + 2) (n + 3)).hom 0) = (0, 0)
        rw [hy, map_zero, map_zero, neg_zero, add_zero]
      obtain ⟨x, hx⟩ := (hke (n + 1) _).mp hc
      change ((D.d n (n + 1)).hom x.1 + (k.f (n + 1)).hom x.2,
        -((C.d (n + 1) (n + 2)).hom x.2)) = (y, 0) at hx
      have hcx : (C.d (n + 1) (n + 2)).hom x.2 = 0 := neg_eq_zero.mp
        (congrArg (fun w : D.X (n + 1) × C.X (n + 2) ↦ w.2) hx)
      obtain ⟨z, hz⟩ := (hd n x.2).mp hcx
      refine ⟨x.1 + (k.f n).hom z, ?_⟩
      rw [map_add, hnat, hz]
      exact congrArg (fun w : D.X (n + 1) × C.X (n + 2) ↦ w.1) hx
    · rintro ⟨z, rfl⟩
      exact congrArg (fun m ↦ m.hom z) (D.d_comp_d n (n + 1) (n + 2))

end SerrePositivity.AlgebraicGeometry
