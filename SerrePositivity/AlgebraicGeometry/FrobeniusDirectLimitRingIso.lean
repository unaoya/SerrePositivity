module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap
public import Mathlib.Algebra.Category.Ring.Basic

/-!
概要：元の環の同型を、同じ Frobenius 順極限の環同型に移す。
方針：元の正逆の環の射を適用し、有限段の元で逆の法則を示す。
規約：元の環と写像を保持し、零環も除外しない。
使われ方：同じ有限族の Γ と Frobenius 係数の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)

/-- 同じ元の正逆の射による、実際の Frobenius 順極限の環同型。 -/
def frobeniusDirectLimitRingIso (e : CommRingCat.of A ≅ CommRingCat.of B) :
    FrobeniusDirectLimit A p hp hA ≃+* FrobeniusDirectLimit B p hp hB :=
  { frobeniusDirectLimitMap p hp hA hB e.hom.hom with
    invFun := frobeniusDirectLimitMap p hp hB hA e.inv.hom
    left_inv := by
      intro x
      obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) x
      change frobeniusDirectLimitOf A p hp hA n (e.inv.hom (e.hom.hom x)) =
        frobeniusDirectLimitOf A p hp hA n x
      exact congrArg (frobeniusDirectLimitOf A p hp hA n)
        (congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of A ↦ g.hom x) e.hom_inv_id)
    right_inv := by
      intro x
      obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap B p hp hB) x
      change frobeniusDirectLimitOf B p hp hB n (e.hom.hom (e.inv.hom x)) =
        frobeniusDirectLimitOf B p hp hB n x
      exact congrArg (frobeniusDirectLimitOf B p hp hB n)
        (congrArg (fun g : CommRingCat.of B ⟶ CommRingCat.of B ↦ g.hom x) e.inv_hom_id) }

/-- 元の各有限段には、同じ環の同型を適用する。 -/
theorem frobeniusDirectLimitRingIso_of (e : CommRingCat.of A ≅ CommRingCat.of B)
    (n : ℕ) (x : A) :
    frobeniusDirectLimitRingIso p hp hA hB e (frobeniusDirectLimitOf A p hp hA n x) =
      frobeniusDirectLimitOf B p hp hB n (e.hom.hom x) := rfl

end SerrePositivity.AlgebraicGeometry
