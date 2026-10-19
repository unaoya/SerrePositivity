module
public import SerrePositivity.InfinityCategories.Derived.DGRoofBoundaryHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofRefinements

/-! # 共通閉細分後の実屋根における有限相対充填

概要：指定屋根の有限境界を一つの閉細分後で充填し、実商屋根内で指定商単体と比較する。
方針：全境界を保つ pinched 充填を行い、境界固定比較を同じ実分母の fiber に含める。
規約：厳密な境界等式は細分後の係数上で述べる。使われ方：元の分母への prism 輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 指定屋根の有限境界は、共通細分後で厳密に充填でき、実商屋根で境界固定比較を持つ。 -/
theorem dgQuotientRoofFinite_exists_actualFillers (P : Set D) (hP : localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (s : DGClosedVerdierDenominators A D P x)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶
      DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) (y i))
    (g : ∀ i, (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
      ((inclusion A D P).obj (y i))) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (Complex A) s.obj.left) (y i)) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i)) :
    ∃ s' : DGClosedVerdierDenominators A D P x, ∃ R : s' ⟶ s,
      ∃ t : ∀ i, (DGNerve.pinchedHom A D
        (ForgetEnrichment.to (Complex A) s'.obj.left) (y i)) _⦋n + 1⦌,
        (∀ i, (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (t i) =
          b i ≫ pinchedClosedPrecomposition A D (y := y i) R.hom.left) ∧
        ∀ i, ∃ H : RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫
            pinchedClosedPrecomposition A (QuotientObject D P)
              (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map R.hom.left) ≫
              dgQuotientClosedRoofHomInclusion A D P x (y i) s')
          (SSet.yonedaEquiv.symm (t i) ≫ dgClosedRoofHomInclusion A D P x (y i) s' ≫
            dgRoofCorrespondenceMap A D P x (y i)),
          H.homotopy.h ≫ dgQuotientRoofCorrespondenceProjection A D P x (y i) =
            SSet.const (dgClosedVerdierDenominatorVertex A D P x s') := by
  obtain ⟨q, r, hr, t, ht, hh⟩ := dgQuotientFinite_exists_actualRelativeHomotopies A D P hP
    (ForgetEnrichment.to (Complex A) s.obj.left) y b g hb
  let s' := dgClosedRoofRefine A D P x s r hr
  let R := dgClosedRoofRefineHom A D P x s r hr
  refine ⟨s', R, fun i => (t i).toPinched, ht, ?_⟩
  intro i
  let H := Classical.choice (hh i)
  have H' : RoofBoundaryFixedHomotopy
      (SSet.yonedaEquiv.symm (g i) ≫ pinchedClosedPrecomposition A (QuotientObject D P)
        (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map r))
      (SSet.yonedaEquiv.symm (t i).toPinched ≫
        pinchedHomChainMap ((inclusion A D P).map q (y i))) := by
    rw [pinchedClosedPrecomposition, pinchedLinearSimplexMap_yoneda,
      SSet.yonedaEquiv_symm_comp]
    exact ⟨H.homotopy, H.boundary⟩
  refine ⟨dgClosedRoofRelativeHomotopy A D P x (y i) s'
    (SSet.yonedaEquiv.symm (g i) ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map r))
    (SSet.yonedaEquiv.symm (t i).toPinched) H', ?_⟩
  exact dgClosedRoofRelativeHomotopy_projection A D P x (y i) s'
    (SSet.yonedaEquiv.symm (g i) ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map r))
    (SSet.yonedaEquiv.symm (t i).toPinched) H'

end SerrePositivity.InfinityCategories
