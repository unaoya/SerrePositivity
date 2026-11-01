module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomPrismDirectNaturality
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransPinchedSlice
public import SerrePositivity.InfinityCategories.Core.Roof.SliceOverEqualityTransport
/-!
概要：直接前合成の固定標的 slice prism と係数自然性を構成する。
方針：直接の閉前合成鎖写像と全二相単体の係数比較を使う。
規約：始域・標的の Small 仮定なしに、元の対象と全係数を保持する。
使われ方：D2 の一般対象宇宙での dg gluing 比較。
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
variable (Q : DGFunctor A D E)

/-- 概要：元の pinched Hom 全体に対する、閉前合成の指定標的 slice 内の実 prism。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgClosedPrecompositionSlicePrismDirect {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    DGNerve.pinchedHom A D q y ⊗ (Δ[1] : SSet.{max u v}) ⟶
      sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)) :=
  (dgWalkingHomPinched A D q y ▷ Δ[1]) ≫
    dgStrictNatTransPinchedSlice A (DGWalkingHom.{u, v} A (homObject A D q y)) D
      (dgWalkingHomPrecomposeNatTransDirect A D y r)
      (dgWalkingHomSource A (homObject A D q y))
      (dgWalkingHomTarget A (homObject A D q y))

/-- 概要：固定標的の等式輸送込みで、閉前合成の全 prism は dg 関手像と可換。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgClosedPrecompositionSlicePrismDirect_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (hp : (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y) ≫ dgNerve.map Q =
      (SSet.yonedaEquiv (X := dgNerve A E)).symm (Simplex.vertex (Q.obj y))) :
    dgClosedPrecompositionSlicePrismDirect A D y r ≫
      sliceOverPostcomp _ (dgNerve.map Q) ≫ (eqToIso (congrArg sliceOver hp)).hom =
      (pinchedHomChainMap (Q.map q y) ▷ (Δ[1] : SSet.{max u v})) ≫
        dgClosedPrecompositionSlicePrismDirect A E (Q.obj y) (Q.onClosed.map r) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((eqToIso (congrArg sliceOver hp)).hom.app _
    ((sliceOverPostcomp _ (dgNerve.map Q)).app _
      ((dgClosedPrecompositionSlicePrismDirect A D y r).app _ s))).val = _
  rw [roofSliceTransport_val hp]
  change ((joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
    ((dgWalkingHomPrecomposeNatTransDirect A D y r).simplex
      ((dgWalkingHomPinched A D q y).app _ s.1).val
      (pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom))) ≫ dgNerve.map Q = _
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  exact congrArg (fun t : Simplex A E (n + 1) => (joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve A E)).symm t)
      (dgWalkingHomPrecomposeDirect_coefficient_naturality A D E Q y r s.1
        (pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom))

end SerrePositivity.InfinityCategories
