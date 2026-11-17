module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitRingIso

/-!
概要：同じ環同型の可換四角を、実際の Frobenius 順極限の環同型に送る。
方針：同じ有限段の元に元の可換四角を適用する。
規約：元の環と射、標数条件を保持する。
使われ方：矩形の係数と開の細分の Frobenius 比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

/-- 同じ元の可換四角に、実際の Frobenius 順極限の環同型は自然。 -/
theorem frobeniusDirectLimitRingIso_naturality (p : ℕ) (hp : p.Prime)
    (hA : (p : A) = 0) (hB : (p : B) = 0) (hC : (p : C) = 0) (hD : (p : D) = 0)
    (e : CommRingCat.of A ≅ CommRingCat.of B) (d : CommRingCat.of C ≅ CommRingCat.of D)
    (f : A →+* C) (g : B →+* D)
    (h : CommRingCat.ofHom f ≫ d.hom = e.hom ≫ CommRingCat.ofHom g)
    (z : FrobeniusDirectLimit A p hp hA) :
    frobeniusDirectLimitRingIso p hp hC hD d (frobeniusDirectLimitMap p hp hA hC f z) =
      frobeniusDirectLimitMap p hp hB hD g (frobeniusDirectLimitRingIso p hp hA hB e z) := by
  obtain ⟨k, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) z
  change frobeniusDirectLimitOf D p hp hD k (d.hom.hom (f x)) =
    frobeniusDirectLimitOf D p hp hD k (g (e.hom.hom x))
  exact congrArg (frobeniusDirectLimitOf D p hp hD k)
    (congrArg (fun q : CommRingCat.Hom _ _ ↦ q.hom x) h)

end SerrePositivity.AlgebraicGeometry
