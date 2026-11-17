module

public import SerrePositivity.AlgebraicGeometry.AugmentedCechCone
public import SerrePositivity.AlgebraicGeometry.CochainComplexOfExactnessReflection

/-!
概要：既存の増大 cone の完全性を、指定した微分の完全性で両向きに読む。
方針：増大項と以後の項に、明示的な複体の完全性の判定を分けて適用する。
規約：既存の全複体とその微分を保持する。
使われ方：共通細分での増大項を含めた完全性の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- 既存の増大 cone の完全性は、増大写像とその先の微分の完全性と同値。 -/
theorem augmentedCechCone_acyclic_iff_injective_exact
    (A B : CochainComplex (ModuleCat.{u} R) ℕ) (f : A ⟶ B)
    (Z : ModuleCat.{u} R) (a : Z →ₗ[R] A.X 0)
    (hc : (cechRefinementConeDifferential A B f 0).comp a = 0) :
    (augmentedCechCone A B f Z a hc).Acyclic ↔
      Function.Injective a ∧ Function.Exact a (cechRefinementConeDifferential A B f 0) ∧
        ∀ n, Function.Exact (cechRefinementConeDifferential A B f n)
          (cechRefinementConeDifferential A B f (n + 1)) := by
  have hdd : ∀ n,
      ModuleCat.ofHom (augmentedCechConeDifferential A B f Z a n) ≫
        ModuleCat.ofHom (augmentedCechConeDifferential A B f Z a (n + 1)) = 0 := by
    intro n
    apply ModuleCat.hom_ext
    exact augmentedCechConeDifferential_squared A B f Z a hc n
  constructor
  · intro h
    obtain ⟨hi, he⟩ := cochainComplexOf_injective_exact_of_acyclic
      (augmentedCechConeTerm A B Z)
      (fun n ↦ ModuleCat.ofHom (augmentedCechConeDifferential A B f Z a n)) hdd h
    exact ⟨hi, he 0, fun n ↦ he (n + 1)⟩
  · rintro ⟨hi, he, hd⟩
    apply cochainComplexOf_acyclic_of_injective_exact _ _ hdd hi
    intro n
    cases n with
    | zero => exact he
    | succ n => exact hd n

end SerrePositivity.AlgebraicGeometry
