module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomPrismNaturality
public import SerrePositivity.InfinityCategories.Derived.DGClosedPrecompositionSlicePrism
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransSliceWhisker

/-! # 閉前合成の実 slice prism の dg 関手自然性

概要：全係数の閉細分 prism は、固定標的の輸送を含めて dg 関手像と可換。
方針：join の台を比較し、自由係数の全二相単体の自然性を使う。
規約：全単体の厳密等式。使われ方：元・商の実屋根 prism の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable [Small.{u} D] [Small.{u} E] (Q : DGFunctor A D E)

/-- 固定標的の等式輸送込みで、閉前合成の全 prism は dg 関手像と可換。 -/
lemma dgClosedPrecompositionSlicePrism_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (hp : (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y) ≫ dgNerve.map Q =
      (SSet.yonedaEquiv (X := dgNerve A E)).symm (Simplex.vertex (Q.obj y))) :
    dgClosedPrecompositionSlicePrism A D y r ≫
      sliceOverPostcomp _ (dgNerve.map Q) ≫ (eqToIso (congrArg sliceOver hp)).hom =
      (pinchedHomChainMap (Q.map q y) ▷ (Δ[1] : SSet.{max u v})) ≫
        dgClosedPrecompositionSlicePrism A E (Q.obj y) (Q.onClosed.map r) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((eqToIso (congrArg sliceOver hp)).hom.app _
    ((sliceOverPostcomp _ (dgNerve.map Q)).app _
      ((dgClosedPrecompositionSlicePrism A D y r).app _ s))).val = _
  rw [roofSliceTransport_val hp]
  change ((joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
    ((dgWalkingHomPrecomposeNatTrans A D y r).simplex
      ((dgWalkingHomPinched A D q y).app _ s.1).val
      (pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom))) ≫ dgNerve.map Q = _
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  exact congrArg (fun t : Simplex A E (n + 1) => (joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve A E)).symm t)
      (dgWalkingHomPrecompose_coefficient_naturality A D E Q y r s.1
        (pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom))

end SerrePositivity.InfinityCategories
