module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareMap

/-!
概要：基底から中心への商の全射性を使い、中心の辺の自然性を他の三つの可換性から導く。
方針：中心の元を基底へ持ち上げ、四角形とスカラー・商の可換性を順に使う。
規約：中心の自然性を追加仮定にしない。完全性も不要。
使われ方：F8 の実際の各比較から全複体の射を作る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare
variable {s t : CechAugmentedSquare.{u} R}

/-- 商が全射なら、中心の辺の可換性は基底・スカラー・制限の可換性から従う。 -/
theorem center_naturality_of_surjective_quotient
    (α : s.C ⟶ t.C) (β : s.E ⟶ t.E)
    (z : s.base →ₗ[R] t.base) (q : s.centerBase →ₗ[R] t.centerBase)
    (hquot : Function.Surjective s.quotient)
    (hsquare : s.restriction ≫ β = α ≫ t.restriction)
    (hscalar : (α.f 0).hom.comp s.scalar = t.scalar.comp z)
    (hquotient : q.comp s.quotient = t.quotient.comp z) :
    (β.f 0).hom.comp s.center = t.center.comp q := by
  apply LinearMap.ext
  intro c
  obtain ⟨a, rfl⟩ := hquot c
  calc
    _ = (β.f 0).hom ((s.restriction.f 0).hom (s.scalar a)) :=
      congrArg (fun x ↦ (β.f 0).hom x) (LinearMap.congr_fun s.commutes a).symm
    _ = (t.restriction.f 0).hom ((α.f 0).hom (s.scalar a)) :=
      congrArg (fun m ↦ (m.f 0).hom (s.scalar a)) hsquare
    _ = (t.restriction.f 0).hom (t.scalar (z a)) :=
      congrArg (fun x ↦ (t.restriction.f 0).hom x) (LinearMap.congr_fun hscalar a)
    _ = t.center (t.quotient (z a)) := LinearMap.congr_fun t.commutes (z a)
    _ = _ := congrArg t.center (LinearMap.congr_fun hquotient a).symm

/-- 基底から中心への全射を使い、三つの辺を保つデータから四角形の射を作る。 -/
def Map.ofSurjectiveQuotient
    (α : s.C ⟶ t.C) (β : s.E ⟶ t.E)
    (z : s.base →ₗ[R] t.base) (q : s.centerBase →ₗ[R] t.centerBase)
    (hquot : Function.Surjective s.quotient)
    (hsquare : s.restriction ≫ β = α ≫ t.restriction)
    (hscalar : (α.f 0).hom.comp s.scalar = t.scalar.comp z)
    (hquotient : q.comp s.quotient = t.quotient.comp z) : Map s t where
  left := α
  right := β
  base := z
  center := q
  restriction := hsquare
  scalar := hscalar
  quotient := hquotient
  center_naturality := center_naturality_of_surjective_quotient
    α β z q hquot hsquare hscalar hquotient

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
