module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofPrismComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofFillerBoundaryTransport

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {s' s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (R : s' ⟶ s)

/-- 商単体の細分輸送の境界と、充填境界の輸送の商像は全時刻で厳密に一致。 -/
lemma dgRoofFillerTransport_boundary {n : ℕ}
    (b : (∂Δ[n] : SSet.{max u v}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) _⦋n⦌)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y) =
        (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm g)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌)
    (ht : (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t =
      b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) R.hom.left) :
    ((∂Δ[n]).ι ▷ (Δ[1] : SSet.{max u v})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofSimplexRefinementHomotopy A D P x y R g).h =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofFillerBoundaryHomotopy A D P x y R b t ht).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y := by
  change ((∂Δ[n]).ι ▷ Δ[1]) ≫ ((SSet.yonedaEquiv.symm g ▷ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofRefinementPrism A D P x y R) =
    ((b ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementPrism A D P x y R) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y
  rw [← Category.assoc, ← comp_whiskerRight, ← hb, comp_whiskerRight, Category.assoc,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementPrism_comparison]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
