module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRoofFiniteFillers

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 任意の指定済み屋根上の有限境界を、同じ屋根への共通細分の後で相対充填できる。 -/
theorem dgQuotientRoofRefinement_relative_fillers (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierRoofDiagram A D P x (y i)).obj (op s))
    (g : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofComparison A D P x (y i)).app (op s) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofConstantComparison A D P x (y i)).app (op s)) :
    ∃ s' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x, ∃ r : s' ⟶ s,
      ∃ t : ∀ i, ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierRoofDiagram A D P x (y i)).obj (op s')) _⦋n + 1⦌,
        (∀ i, (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (t i) =
          b i ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierRoofDiagram A D P x (y i)).map r.op) ∧
        ∀ i, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofConstantComparison A D P x (y i)).app (op s'))
          (SSet.yonedaEquiv.symm (t i) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofComparison A D P x (y i)).app (op s'))) := by
  let q := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left
  let g' := fun i => ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofConstantComparison A D P x (y i)).app (op s)).app
    (Opposite.op ⦋n + 1⦌) (g i)
  have hb' (i) : b i ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map q (y i)) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g' i) := by
    rw [show SSet.yonedaEquiv.symm (g' i) = SSet.yonedaEquiv.symm (g i) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofConstantComparison A D P x (y i)).app (op s) by
        rw [SSet.yonedaEquiv_symm_comp]
        rfl]
    exact hb i
  obtain ⟨p, r, hr, t, ht, hh⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_actualRelativeHomotopies A D P hP q y b g' hb'
  let s' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefine A D P x s r hr
  let R := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefineHom A D P x s r hr
  refine ⟨s', R, fun i => (t i).toPinched, ht, ?_⟩
  intro i
  let H := Classical.choice (hh i)
  have hstart := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofConstantComparison_refine A D P x (y i) s r hr (g i)
  rw [← hstart]
  change Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy
    (SSet.yonedaEquiv.symm (g' i) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap _)
    (SSet.yonedaEquiv.symm (t i).toPinched ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap _))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap_yoneda, SSet.yonedaEquiv_symm_comp]
  exact ⟨⟨H.homotopy, H.boundary⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
