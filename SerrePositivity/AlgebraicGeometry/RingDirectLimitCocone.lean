module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder

/-!
概要：既存の代数的な環の順極限を、同じ環の圏論的余極限と比較する。
方針：同じ標準写像と環の lift・hom_ext の普遍性をそのまま使う。
規約：元の環と遷移の環準同型を保持する。
使われ方：Frobenius の実際の環・矢印の余極限と conerve の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (f · · ·)]

/-- 実際の環準同型の有向系を、同じ環の図式にする。 -/
def ringDirectSystemFunctor : ℕ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (A n)
  map h := CommRingCat.ofHom (f _ _ (leOfHom h))
  map_id n := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact DirectedSystem.map_self' f x
  map_comp h k := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (DirectedSystem.map_map' f (leOfHom h) (leOfHom k) x).symm

/-- 代数的な環の順極限への同じ標準写像の余錐。 -/
def ringDirectSystemCocone : Cocone (ringDirectSystemFunctor f) where
  pt := CommRingCat.of (DirectLimit A f)
  ι :=
    { app := fun n ↦ CommRingCat.ofHom (DirectLimit.Ring.of A f n)
      naturality := by
        intro i j h
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        exact DirectLimit.Ring.of_f (leOfHom h) x }

/-- 同じ環の lift と hom_ext は、同じ余錐の圏論的余極限の普遍性を与える。 -/
def ringDirectSystemIsColimit : IsColimit (ringDirectSystemCocone f) where
  desc c := CommRingCat.ofHom (DirectLimit.Ring.lift A f c.pt
    (fun n ↦ (c.ι.app n).hom) (by
      intro i j h x
      exact congrArg (fun g ↦ g.hom x) (c.w (homOfLE h))))
  fac c j := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl
  uniq c m hm := by
    apply CommRingCat.hom_ext
    apply DirectLimit.Ring.hom_ext
    intro n
    apply RingHom.ext
    intro x
    exact congrArg (fun g ↦ g.hom x) (hm n)

/-- 代数的な環の順極限と、同じ図式の圏論的余極限の標準同型。 -/
def ringDirectLimitColimitIso :
    CommRingCat.of (DirectLimit A f) ≅ colimit (ringDirectSystemFunctor f) :=
  (ringDirectSystemIsColimit f).coconePointUniqueUpToIso
    (colimit.isColimit (ringDirectSystemFunctor f))

/-- 標準同型は、各有限段からの同じ環の標準写像を保つ。 -/
theorem ringDirectLimitColimitIso_ι (n : ℕ) :
    CommRingCat.ofHom (DirectLimit.Ring.of A f n) ≫ (ringDirectLimitColimitIso f).hom =
      colimit.ι (ringDirectSystemFunctor f) n :=
  (ringDirectSystemIsColimit f).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (ringDirectSystemFunctor f)) n

end SerrePositivity.AlgebraicGeometry
