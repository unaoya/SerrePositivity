module
public import SerrePositivity.InfinityCategories.Derived.DGRoofPrismComparison
public import SerrePositivity.InfinityCategories.Derived.DGRoofFillerBoundaryTransport

/-! # 実屋根充填の二輸送の境界整合性

概要：指定商単体の輸送の境界は、元の充填境界の輸送を商へ写したものと一致する。
方針：入力の厳密境界等式を全 prism の商自然性へ渡す。
規約：境界と全時刻上の射の厳密等式。使われ方：二重 prism の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {s' s : DGClosedVerdierDenominators A D P x} (R : s' ⟶ s)

/-- 商単体の細分輸送の境界と、充填境界の輸送の商像は全時刻で厳密に一致。 -/
lemma dgRoofFillerTransport_boundary {n : ℕ}
    (b : (∂Δ[n] : SSet.{max u v}) ⟶
      DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (g : (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
      ((DGQuotient.inclusion A D P).obj y)) _⦋n⦌)
    (hb : b ≫ pinchedHomChainMap ((DGQuotient.inclusion A D P).map
      (ForgetEnrichment.to (Complex A) s.obj.left) y) =
        (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm g)
    (t : (DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌)
    (ht : (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t =
      b ≫ pinchedClosedPrecomposition A D (y := y) R.hom.left) :
    ((∂Δ[n]).ι ▷ (Δ[1] : SSet.{max u v})) ≫
      (dgQuotientRoofSimplexRefinementHomotopy A D P x y R g).h =
      (dgClosedRoofFillerBoundaryHomotopy A D P x y R b t ht).h ≫
        dgRoofCorrespondenceMap A D P x y := by
  change ((∂Δ[n]).ι ▷ Δ[1]) ≫ ((SSet.yonedaEquiv.symm g ▷ Δ[1]) ≫
    dgQuotientClosedRoofRefinementPrism A D P x y R) =
    ((b ▷ Δ[1]) ≫ dgClosedRoofRefinementPrism A D P x y R) ≫
      dgRoofCorrespondenceMap A D P x y
  rw [← Category.assoc, ← comp_whiskerRight, ← hb, comp_whiskerRight, Category.assoc,
    Category.assoc, dgClosedRoofRefinementPrism_comparison]

end SerrePositivity.InfinityCategories
