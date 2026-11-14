module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.PolynomialCategory
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffinePolynomial
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons

/-!
# 完備多項式代数の関手性

## 概要
剰余環上の多項式代数の代入を、p 完備多項式代数へ延長する。

## 方針
多項式代入を主完備化の普遍性で延長し、単位との可換性から恒等と合成を得る。

## 規約
完備化の標準射は `prismPolynomialUnit`。

## 使われ方
BS 著者版 Construction 4.18 の大きい枠における添字写像。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

local notation "k" => (A ⧸ P.ideal)

/-- 完備多項式環からの環準同型は、未完備多項式への制限で決まる。 -/
theorem polyCompletion_hom_ext {r t : ℕ} {f g : polyCompletion P r →+* polyCompletion P t}
    (h : f.comp (prismPolynomialUnit P (Fin r)) = g.comp (prismPolynomialUnit P (Fin r))) :
    f = g := by
  let z := f.comp (prismPolynomialUnit P (Fin r))
  let := z.toAlgebra
  have hc : IsModuleComplete (MvPolynomial (Fin r) k) (p : MvPolynomial (Fin r) k)
      (ModuleCat.of _ (polyCompletion P t)) := by
    apply (isModuleComplete_algebraMap_iff (MvPolynomial (Fin r) k) (polyCompletion P t)
      (p : MvPolynomial (Fin r) k) (polyCompletion P t)).mp
    change IsModuleComplete (polyCompletion P t) (z (p : MvPolynomial (Fin r) k)) _
    rw [map_natCast, ← map_natCast (prismPolynomialUnit P (Fin t)) p]
    have H := principalCompletion_isModuleComplete_unit (p : MvPolynomial (Fin t) k)
    rw [isModuleComplete_iff_recurrence_bijective] at H ⊢
    exact H
  exact (principalCompletion_existsUnique_ringHom _ _ _ z hc).unique rfl h.symm

/-- 剰余環上の多項式代入を p 完備化した代数射。 -/
def polyCompletionMap {Q Q' : Poly k} (f : Q ⟶ Q') :
    polyCompletion P Q.n →ₐ[k] polyCompletion P Q'.n := by
  let g := (Poly.hom f).toRingHom
  let a : MvPolynomial (Fin Q.n) k := p
  let b : MvPolynomial (Fin Q'.n) k := p
  refine ⟨principalCompletionMap g a b (map_natCast g p), ?_⟩
  intro x
  change principalCompletionMap g a b (map_natCast g p) (prismPolynomialUnit P (Fin Q.n)
    (MvPolynomial.C x)) = prismPolynomialUnit P (Fin Q'.n) (MvPolynomial.C x)
  exact (RingHom.congr_fun (principalCompletionMap_comp g a b (map_natCast g p)) _).trans
    (congrArg (prismPolynomialUnit P (Fin Q'.n)) ((Poly.hom f).commutes x))

/-- 完備化した代入は未完備環の標準射と可換。 -/
@[simp] theorem polyCompletionMap_unit {Q Q' : Poly k} (f : Q ⟶ Q')
    (x : MvPolynomial (Fin Q.n) k) :
    polyCompletionMap P f (prismPolynomialUnit P (Fin Q.n) x) =
      prismPolynomialUnit P (Fin Q'.n) (Poly.hom f x) := by
  let g := (Poly.hom f).toRingHom
  exact RingHom.congr_fun
    (principalCompletionMap_comp g (p : MvPolynomial (Fin Q.n) k)
      (p : MvPolynomial (Fin Q'.n) k) (map_natCast g p)) x

/-- 完備化した代入は恒等を保つ。 -/
@[simp] theorem polyCompletionMap_id (Q : Poly k) :
    polyCompletionMap P (𝟙 Q) = AlgHom.id k _ := by
  apply AlgHom.toRingHom_injective
  apply polyCompletion_hom_ext P
  apply RingHom.ext
  intro x
  exact polyCompletionMap_unit P (𝟙 Q) x

/-- 完備化した代入は合成を保つ。 -/
theorem polyCompletionMap_comp {Q Q' Q'' : Poly k} (f : Q ⟶ Q') (g : Q' ⟶ Q'') :
    polyCompletionMap P (f ≫ g) = (polyCompletionMap P g).comp (polyCompletionMap P f) := by
  apply AlgHom.toRingHom_injective
  apply polyCompletion_hom_ext P
  apply RingHom.ext
  intro x
  change polyCompletionMap P (f ≫ g) (prismPolynomialUnit P (Fin Q.n) x) =
    polyCompletionMap P g (polyCompletionMap P f (prismPolynomialUnit P (Fin Q.n) x))
  simp only [polyCompletionMap_unit]
  rfl

end SerrePositivity.BhattScholze.Prismatic
