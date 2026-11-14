module

public import SerrePositivity.AlgebraicGeometry.LinearDirectLimitComparison
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Category.Preorder

/-!
概要：有限段の元で計算した加群の順極限を、圏論的な余極限と比較する。
方針：段ごとの標準写像の余錐を作り、線形写像の普遍性を適用する。
規約：自然数の有向系の実際の遷移を、そのまま関手の射に使う。
使われ方：F6 の代数的な順極限を、2e の filtered 余極限と Čech H の比較へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R] {M : ℕ → Type u}
variable [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
variable (f : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable [DirectedSystem M (f · · ·)]

/-- 線形写像の実際の有向系を加群圏の関手にする。 -/
def linearDirectSystemFunctor : ℕ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (M n)
  map h := ModuleCat.ofHom (f _ _ (leOfHom h))
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact DirectedSystem.map_self' f x
  map_comp h k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (DirectedSystem.map_map' f (leOfHom h) (leOfHom k) x).symm

/-- 代数的な順極限の標準写像は、実際の有向系の余錐。 -/
def linearDirectSystemCocone : Cocone (linearDirectSystemFunctor f) where
  pt := ModuleCat.of R (DirectLimit M f)
  ι :=
    { app := fun n ↦ ModuleCat.ofHom (DirectLimit.Module.of R ℕ M f n)
      naturality := by
        intro i j h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact DirectLimit.Module.of_f }

/-- 代数的な順極限の線形写像の普遍性は、加群圏の余極限の普遍性を与える。 -/
def linearDirectSystemIsColimit : IsColimit (linearDirectSystemCocone f) where
  desc c := ModuleCat.ofHom (DirectLimit.Module.lift R ℕ M f
    (fun n ↦ (c.ι.app n).hom) (by
      intro i j h x
      exact congrArg (fun g ↦ g.hom x) (c.w (homOfLE h))))
  fac c j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  uniq c m hm := by
    apply ModuleCat.hom_ext
    apply DirectLimit.Module.hom_ext
    intro n
    apply LinearMap.ext
    intro x
    exact congrArg (fun g ↦ g.hom x) (hm n)

/-- 代数的な順極限と、同じ関手の圏論的な余極限の標準同型。 -/
def linearDirectLimitColimitIso :
    ModuleCat.of R (DirectLimit M f) ≅ colimit (linearDirectSystemFunctor f) :=
  (linearDirectSystemIsColimit f).coconePointUniqueUpToIso
    (colimit.isColimit (linearDirectSystemFunctor f))

end SerrePositivity.AlgebraicGeometry
