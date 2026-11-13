module

public import SerrePositivity.AlgebraicGeometry.AugmentedCechCone
public import SerrePositivity.AlgebraicGeometry.CechRefinementConeMap

/-!
概要：増大項付き cone の全複体を可換四角と増大写像を保つ射に自然にする。
方針：増大項には基底の射、その先には既存の cone の射を適用する。
規約：係数環と加群の宇宙を分離し、整数係数でも使う。
使われ方：F8 の共通細分・底変換・閉厚化・Frobenius の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable {A B A' B' A'' B'' : CochainComplex (ModuleCat.{u} R) ℕ}
variable {f : A ⟶ B} {f' : A' ⟶ B'}
variable {Z Z' Z'' : ModuleCat.{u} R}
variable {a : Z →ₗ[R] A.X 0} {a' : Z' →ₗ[R] A'.X 0}

/-- 全複体の各項の射。増大項では基底の射、その後は cone の各項の射。 -/
def augmentedCechConeMapTerm (α : A ⟶ A') (β : B ⟶ B') (ζ : Z →ₗ[R] Z') :
    ∀ n, augmentedCechConeTerm A B Z n →ₗ[R] augmentedCechConeTerm A' B' Z' n
  | 0 => ζ
  | n + 1 => cechRefinementConeMapTerm α β n

/-- 可換四角と増大写像の自然性により、全複体の各項の射は微分と可換。 -/
theorem augmentedCechConeMapTerm_differential
    (α : A ⟶ A') (β : B ⟶ B') (ζ : Z →ₗ[R] Z')
    (hsquare : f ≫ β = α ≫ f')
    (haug : (α.f 0).hom.comp a = a'.comp ζ) (n : ℕ) :
    (augmentedCechConeMapTerm α β ζ (n + 1)).comp
      (augmentedCechConeDifferential A B f Z a n) =
    (augmentedCechConeDifferential A' B' f' Z' a' n).comp
      (augmentedCechConeMapTerm α β ζ n) := by
  cases n with
  | zero => exact haug
  | succ n => exact cechRefinementConeMapTerm_differential α β hsquare n

/-- 可換四角と増大写像を保つ射が誘導する、増大項付き全複体の余鎖写像。 -/
def augmentedCechConeMap
    (hc : (cechRefinementConeDifferential A B f 0).comp a = 0)
    (hc' : (cechRefinementConeDifferential A' B' f' 0).comp a' = 0)
    (α : A ⟶ A') (β : B ⟶ B') (ζ : Z →ₗ[R] Z')
    (hsquare : f ≫ β = α ≫ f')
    (haug : (α.f 0).hom.comp a = a'.comp ζ) :
    augmentedCechCone A B f Z a hc ⟶ augmentedCechCone A' B' f' Z' a' hc' :=
  CochainComplex.ofHom
    (fun n ↦ { hom' := augmentedCechConeMapTerm α β ζ n }) (by
      intro n
      simp only [augmentedCechCone, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      exact (augmentedCechConeMapTerm_differential α β ζ hsquare haug n).symm)

/-- 全複体の各項への写像は成分の合成を保つ。 -/
theorem augmentedCechConeMapTerm_comp
    (α : A ⟶ A') (β : B ⟶ B') (ζ : Z →ₗ[R] Z')
    (α' : A' ⟶ A'') (β' : B' ⟶ B'') (ζ' : Z' →ₗ[R] Z'') (n : ℕ) :
    (augmentedCechConeMapTerm α' β' ζ' n).comp (augmentedCechConeMapTerm α β ζ n) =
      augmentedCechConeMapTerm (α ≫ α') (β ≫ β') (ζ'.comp ζ) n := by
  cases n with
  | zero => rfl
  | succ n => exact cechRefinementConeMapTerm_comp α β α' β' n

/-- 全複体の各項への恒等写像。 -/
theorem augmentedCechConeMapTerm_id (n : ℕ) :
    augmentedCechConeMapTerm (𝟙 A) (𝟙 B) (LinearMap.id : Z →ₗ[R] Z) n = LinearMap.id := by
  cases n with
  | zero => rfl
  | succ n => exact cechRefinementConeMapTerm_id n

end SerrePositivity.AlgebraicGeometry
