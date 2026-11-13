module

public import SerrePositivity.AlgebraicGeometry.CechConeHomologyExactness
public import SerrePositivity.AlgebraicGeometry.CochainComplexOfExactness

/-!
概要：非負次数の cone の前に増大項を付けた明示的な全複体と、その完全性判定。
方針：増大項の完全性を零次・一次に、H の情報による cone の計算を以後の次数に使う。
規約：各項と微分を指定し、acyclicity は Mathlib の HomologicalComplex.Acyclic で述べる。
使われ方：F8 のブローアップ四角形の全複体。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable (A B : CochainComplex (ModuleCat.{u} R) ℕ) (f : A ⟶ B)
variable (Z : ModuleCat.{u} R) (a : Z →ₗ[R] A.X 0)

/-- 増大項、元の零次項、以後の二つの項の直積からなる全複体の各項。 -/
def augmentedCechConeTerm : ℕ → ModuleCat.{u} R
  | 0 => Z
  | n + 1 => cechRefinementConeTerm A B n

/-- 増大項では指定した写像、その先では既存の cone の微分。 -/
def augmentedCechConeDifferential :
    ∀ n, augmentedCechConeTerm A B Z n →ₗ[R] augmentedCechConeTerm A B Z (n + 1)
  | 0 => a
  | n + 1 => cechRefinementConeDifferential A B f n

/-- 増大写像がサイクルへ入るなら、明示的な全微分の二乗は零。 -/
theorem augmentedCechConeDifferential_squared
    (hcycle : (cechRefinementConeDifferential A B f 0).comp a = 0) (n : ℕ) :
    (augmentedCechConeDifferential A B f Z a (n + 1)).comp
      (augmentedCechConeDifferential A B f Z a n) = 0 := by
  cases n with
  | zero => exact hcycle
  | succ n => exact cechRefinementConeDifferential_squared A B f n

/-- 各項と微分を指定した、増大項付き cone の全複体。 -/
def augmentedCechCone
    (hcycle : (cechRefinementConeDifferential A B f 0).comp a = 0) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (augmentedCechConeTerm A B Z)
    (fun n ↦ ModuleCat.ofHom (augmentedCechConeDifferential A B f Z a n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact augmentedCechConeDifferential_squared A B f Z a hcycle n)

/-- 増大項の単射・零次での完全性と、H⁰ の全射・正次数の同型から全複体は acyclic。 -/
theorem augmentedCechCone_acyclic
    (hcycle : (cechRefinementConeDifferential A B f 0).comp a = 0)
    (hinj : Function.Injective a)
    (hexact : Function.Exact a (cechRefinementConeDifferential A B f 0))
    (hzero : Function.Surjective (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ) 0 0 1).map f)).hom)
    (hpos : ∀ n, Function.Bijective (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        n (n + 1) (n + 2)).map f)).hom) :
    (augmentedCechCone A B f Z a hcycle).Acyclic := by
  apply cochainComplexOf_acyclic_of_injective_exact
  · intro n
    apply ModuleCat.hom_ext
    exact augmentedCechConeDifferential_squared A B f Z a hcycle n
  · exact hinj
  · intro n
    cases n with
    | zero => exact hexact
    | succ n =>
      change Function.Exact (cechRefinementConeDifferential A B f n)
        (cechRefinementConeDifferential A B f (n + 1))
      intro x
      constructor
      · exact cechRefinementCone_cycle_boundary_of_homology A B f hzero hpos n x
      · rintro ⟨y, rfl⟩
        exact LinearMap.congr_fun (cechRefinementConeDifferential_squared A B f n) y

end SerrePositivity.AlgebraicGeometry
