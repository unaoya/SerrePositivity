module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic

/-!
概要：実際の切断環の同型を、Frobenius 順極限の整数加群の同型へ送る。
方針：既存の環の射の順極限に同型の正逆を適用する。
規約：零環や空の標準開の環も除外しない。
使われ方：非空の標準開交叉で、斉次局所化の係数と実際の構造層の係数を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)

/-- 環の同型が誘導する、実際の Frobenius 順極限の整数加群の同型。 -/
def frobeniusDirectLimitModuleIso (e : CommRingCat.of A ≅ CommRingCat.of B) :
    ModuleCat.of ℤ (FrobeniusDirectLimit A p hp hA) ≅
      ModuleCat.of ℤ (FrobeniusDirectLimit B p hp hB) where
  hom := ModuleCat.ofHom
    (frobeniusDirectLimitMap p hp hA hB e.hom.hom).toAddMonoidHom.toIntLinearMap
  inv := ModuleCat.ofHom
    (frobeniusDirectLimitMap p hp hB hA e.inv.hom).toAddMonoidHom.toIntLinearMap
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) x
    change frobeniusDirectLimitOf A p hp hA n (e.inv.hom (e.hom.hom x)) =
      frobeniusDirectLimitOf A p hp hA n x
    exact congrArg (frobeniusDirectLimitOf A p hp hA n)
      (congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of A ↦ f.hom x) e.hom_inv_id)
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap B p hp hB) x
    change frobeniusDirectLimitOf B p hp hB n (e.hom.hom (e.inv.hom x)) =
      frobeniusDirectLimitOf B p hp hB n x
    exact congrArg (frobeniusDirectLimitOf B p hp hB n)
      (congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of B ↦ f.hom x) e.inv_hom_id)

/-- 同型の比較は、有限段の元に実際の環の同型を適用する。 -/
theorem frobeniusDirectLimitModuleIso_of
    (e : CommRingCat.of A ≅ CommRingCat.of B) (n : ℕ) (x : A) :
    (frobeniusDirectLimitModuleIso p hp hA hB e).hom.hom
        (frobeniusDirectLimitOf A p hp hA n x) =
      frobeniusDirectLimitOf B p hp hB n (e.hom.hom x) := rfl

end SerrePositivity.AlgebraicGeometry
