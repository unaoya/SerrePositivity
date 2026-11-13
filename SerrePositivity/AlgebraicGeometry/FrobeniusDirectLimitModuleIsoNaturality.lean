module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitModuleIso

/-!
概要：環の同型が誘導する Frobenius 順極限の比較は、可換四角に自然。
方針：有限段の元を使い、同じ環の可換四角の等式を適用する。
規約：具体的なスキームの型を展開しない。
使われ方：実際の閉厚化の係数比較と制限の可換性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

/-- 環の同型の可換四角は、実際の Frobenius 順極限の整数加群でも可換。 -/
theorem frobeniusDirectLimitModuleIso_naturality (p : ℕ) (hp : p.Prime)
    (hA : (p : A) = 0) (hB : (p : B) = 0) (hC : (p : C) = 0) (hD : (p : D) = 0)
    (e : CommRingCat.of A ≅ CommRingCat.of B) (d : CommRingCat.of C ≅ CommRingCat.of D)
    (f : A →+* C) (g : B →+* D) (h : ∀ x, d.hom.hom (f x) = g (e.hom.hom x)) :
    ModuleCat.ofHom (frobeniusDirectLimitMap p hp hA hC f).toAddMonoidHom.toIntLinearMap ≫
        (frobeniusDirectLimitModuleIso p hp hC hD d).hom =
      (frobeniusDirectLimitModuleIso p hp hA hB e).hom ≫
        ModuleCat.ofHom (frobeniusDirectLimitMap p hp hB hD g).toAddMonoidHom.toIntLinearMap := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) x
  change frobeniusDirectLimitOf D p hp hD n (d.hom.hom (f x)) =
    frobeniusDirectLimitOf D p hp hD n (g (e.hom.hom x))
  exact congrArg (frobeniusDirectLimitOf D p hp hD n) (h x)

end SerrePositivity.AlgebraicGeometry
