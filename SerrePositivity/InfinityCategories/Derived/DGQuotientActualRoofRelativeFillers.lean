module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientActualRoofFillers
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofRelativeFiller

/-! # 有限族の実屋根相対充填と全分母射影

概要：任意の有限族に対し、一つの共通閉細分で実相対充填のデータを同時に得る。
方針：細分後の係数の厳密充填と、二つの全係数 prism と境界固定比較を束ねる。
規約：三つのホモトピーの分母射影を厳密に保持する。使われ方：β3 の有限比較の主入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 有限境界と指定商単体を、一つの細分で実充填・全輸送・全分母射影へ接続する。 -/
theorem dgQuotientRoofFinite_exists_relativeFillerData (P : Set D) (hP : localKFlat A D P)
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
        ∀ i, Nonempty (DGActualRoofRelativeFiller A D P x (y i) R (b i) (g i) (t i)) := by
  obtain ⟨s', R, t, ht, hh⟩ := dgQuotientRoofFinite_exists_actualFillers A D P hP x y s b g hb
  refine ⟨s', R, t, ?_⟩
  intro i
  obtain ⟨H, hH⟩ := hh i
  exact ⟨{
    coefficient_boundary := ht i
    boundary_transport := dgClosedRoofFillerBoundaryHomotopy A D P x (y i) R (b i) (t i) (ht i)
    boundary_over :=
      dgClosedRoofFillerBoundaryHomotopy_projection A D P x (y i) R (b i) (t i) (ht i)
    target_transport := dgQuotientRoofSimplexRefinementHomotopy A D P x (y i) R (g i)
    target_over := dgQuotientRoofSimplexRefinementHomotopy_projection A D P x (y i) R (g i)
    transport_boundary := fun h =>
      dgRoofFillerTransport_boundary A D P x (y i) R (b i) (g i) h (t i) (ht i)
    comparison := H
    comparison_over := hH }⟩

end SerrePositivity.InfinityCategories
