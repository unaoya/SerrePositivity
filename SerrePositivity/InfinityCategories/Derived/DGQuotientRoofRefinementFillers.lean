module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRoofFiniteFillers

/-! # 指定済み屋根を保つ有限相対充填

概要：既存の屋根上の指定境界を、その屋根への実際の細分射の後で同時に充填する。
方針：元の始域で有限実相対充填を行い、分母を合成し、定値比較の自然性で目標を戻す。
規約：既存の屋根と指定商単体を保つ。使われ方：屋根図式の余極限比較の細分条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGQuotient DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 任意の指定済み屋根上の有限境界を、同じ屋根への共通細分の後で相対充填できる。 -/
theorem dgQuotientRoofRefinement_relative_fillers (P : Set D) (hP : localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (s : DGClosedVerdierDenominators A D P x)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶
      (dgClosedVerdierRoofDiagram A D P x (y i)).obj (op s))
    (g : ∀ i, (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj x) ((inclusion A D P).obj (y i))) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ (dgQuotientRoofComparison A D P x (y i)).app (op s) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i) ≫
        (dgQuotientRoofConstantComparison A D P x (y i)).app (op s)) :
    ∃ s' : DGClosedVerdierDenominators A D P x, ∃ r : s' ⟶ s,
      ∃ t : ∀ i, ((dgClosedVerdierRoofDiagram A D P x (y i)).obj (op s')) _⦋n + 1⦌,
        (∀ i, (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (t i) =
          b i ≫ (dgClosedVerdierRoofDiagram A D P x (y i)).map r.op) ∧
        ∀ i, Nonempty (RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫
            (dgQuotientRoofConstantComparison A D P x (y i)).app (op s'))
          (SSet.yonedaEquiv.symm (t i) ≫
            (dgQuotientRoofComparison A D P x (y i)).app (op s'))) := by
  let q := ForgetEnrichment.to (Complex A) s.obj.left
  let g' := fun i => ((dgQuotientRoofConstantComparison A D P x (y i)).app (op s)).app
    (Opposite.op ⦋n + 1⦌) (g i)
  have hb' (i) : b i ≫ pinchedHomChainMap ((inclusion A D P).map q (y i)) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g' i) := by
    rw [show SSet.yonedaEquiv.symm (g' i) = SSet.yonedaEquiv.symm (g i) ≫
      (dgQuotientRoofConstantComparison A D P x (y i)).app (op s) by
        rw [SSet.yonedaEquiv_symm_comp]
        rfl]
    exact hb i
  obtain ⟨p, r, hr, t, ht, hh⟩ :=
    dgQuotientFinite_exists_actualRelativeHomotopies A D P hP q y b g' hb'
  let s' := dgClosedRoofRefine A D P x s r hr
  let R := dgClosedRoofRefineHom A D P x s r hr
  refine ⟨s', R, fun i => (t i).toPinched, ht, ?_⟩
  intro i
  let H := Classical.choice (hh i)
  have hstart := dgQuotientRoofConstantComparison_refine A D P x (y i) s r hr (g i)
  rw [← hstart]
  change Nonempty (RoofBoundaryFixedHomotopy
    (SSet.yonedaEquiv.symm (g' i) ≫ pinchedHomChainMap _)
    (SSet.yonedaEquiv.symm (t i).toPinched ≫ pinchedHomChainMap _))
  rw [pinchedLinearSimplexMap_yoneda, SSet.yonedaEquiv_symm_comp]
  exact ⟨⟨H.homotopy, H.boundary⟩⟩

end SerrePositivity.InfinityCategories
