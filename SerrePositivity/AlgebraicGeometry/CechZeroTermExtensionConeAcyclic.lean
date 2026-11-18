module

public import SerrePositivity.AlgebraicGeometry.CechZeroTermExtensionMap
public import SerrePositivity.AlgebraicGeometry.CechRefinementCone
public import SerrePositivity.AlgebraicGeometry.CochainComplexOfExactnessReflection

/-!
概要：零次項を同型な係数で拡張した比較の cone の完全性。
方針：余分な係数の単射性・全射性を零次・一次で使い、以後は元の cone に戻す。
規約：実際の零次項拡張の写像を保持する。
使われ方：共通細分での射影四角形の全複体の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable {C C' : CochainComplex (ModuleCat.{u} R) ℕ}
variable {Q Q' : ModuleCat.{u} R}

set_option backward.isDefEq.respectTransparency false in
/-- 零次項拡張の同型な係数移送は、比較の cone の完全性を保つ。 -/
theorem cechZeroTermExtensionMap_cone_acyclic
    (α : C ⟶ C') (q : Q →ₗ[R] Q')
    (hα : (cechRefinementCone C C' α).Acyclic) (hq : Function.Bijective q) :
    (cechRefinementCone (cechZeroTermExtension C Q) (cechZeroTermExtension C' Q')
      (cechZeroTermExtensionMap α q)).Acyclic := by
  obtain ⟨hi, he⟩ := cochainComplexOf_injective_exact_of_acyclic
    (cechRefinementConeTerm C C')
    (fun n ↦ ModuleCat.ofHom (cechRefinementConeDifferential C C' α n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact cechRefinementConeDifferential_squared C C' α n) hα
  change Function.Injective (cechRefinementConeDifferential C C' α 0) at hi
  change ∀ n, Function.Exact (cechRefinementConeDifferential C C' α n)
    (cechRefinementConeDifferential C C' α (n + 1)) at he
  apply cochainComplexOf_acyclic_of_injective_exact
  · intro n
    apply ModuleCat.hom_ext
    exact cechRefinementConeDifferential_squared _ _ _ n
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    change (((α.f 0).hom x.1, q x.2), -((C.d 0 1).hom x.1)) = ((0, 0), 0) at hx
    have hpair : cechRefinementConeDifferential C C' α 0 x.1 = 0 := by
      change ((α.f 0).hom x.1, -((C.d 0 1).hom x.1)) = (0, 0)
      have h1 : (α.f 0).hom x.1 = 0 := congrArg (fun z : (C'.X 0 × Q') × C.X 1 ↦ z.1.1) hx
      have h2 : -((C.d 0 1).hom x.1) = 0 :=
        congrArg (fun z : (C'.X 0 × Q') × C.X 1 ↦ z.2) hx
      exact Prod.ext h1 h2
    have hx1 : x.1 = 0 := (injective_iff_map_eq_zero _).mp hi _ hpair
    have hx2 : x.2 = 0 := hq.1 ((congrArg (fun z ↦ z.1.2) hx).trans (map_zero q).symm)
    exact Prod.ext hx1 hx2
  · intro n x
    constructor
    · intro hx
      cases n with
      | zero =>
        have hc : cechRefinementConeDifferential C C' α 1 (x.1.1, x.2) = 0 := by
          change ((C'.d 0 1).hom x.1.1 + (α.f 1).hom x.2,
            -((C.d 1 2).hom x.2)) = (0, 0) at hx ⊢
          exact hx
        obtain ⟨y, hy⟩ := (he 0 _).mp hc
        change ((α.f 0).hom y, -((C.d 0 1).hom y)) = (x.1.1, x.2) at hy
        obtain ⟨z, hz⟩ := hq.2 x.1.2
        refine ⟨(y, z), ?_⟩
        change (((α.f 0).hom y, q z), -((C.d 0 1).hom y)) = x
        apply Prod.ext
        · have h1 : (α.f 0).hom y = x.1.1 :=
            congrArg (fun w : C'.X 0 × C.X 1 ↦ w.1) hy
          exact Prod.ext h1 hz
        · exact congrArg (fun w : C'.X 0 × C.X 1 ↦ w.2) hy
      | succ n =>
        have hc : cechRefinementConeDifferential C C' α (n + 2) x = 0 := by
          simp only [cechRefinementConeDifferential, cechZeroTermExtension_d] at hx
          change ((C'.d (n + 1) (n + 2)).hom x.1 + (α.f (n + 2)).hom x.2,
            -((C.d (n + 2) (n + 3)).hom x.2)) = (0, 0) at hx ⊢
          exact hx
        obtain ⟨y, hy⟩ := (he (n + 1) _).mp hc
        cases n with
        | zero =>
          refine ⟨((y.1, 0), y.2), ?_⟩
          change ((C'.d 0 1).hom y.1 + (α.f 1).hom y.2,
            -((C.d 1 2).hom y.2)) = x at hy ⊢
          exact hy
        | succ n =>
          refine ⟨y, ?_⟩
          simp only [cechRefinementConeDifferential, cechZeroTermExtension_d]
          change ((C'.d (n + 1) (n + 2)).hom y.1 + (α.f (n + 2)).hom y.2,
            -((C.d (n + 2) (n + 3)).hom y.2)) = x at hy ⊢
          exact hy
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun (cechRefinementConeDifferential_squared _ _ _ n) y

end SerrePositivity.AlgebraicGeometry
