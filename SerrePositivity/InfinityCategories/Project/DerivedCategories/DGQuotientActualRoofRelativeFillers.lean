module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientActualRoofFillers
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofRelativeFiller

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 有限境界と指定商単体を、一つの細分で実充填・全輸送・全分母射影へ接続する。 -/
theorem dgQuotientRoofFinite_exists_relativeFillerData (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) (y i))
    (g : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) (y i)) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i)) :
    ∃ s' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x, ∃ R : s' ⟶ s,
      ∃ t : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s'.obj.left) (y i)) _⦋n + 1⦌,
        ∀ i, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofRelativeFiller A D P x (y i) R (b i) (g i) (t i)) := by
  obtain ⟨s', R, t, ht, hh⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofFinite_exists_actualFillers A D P hP x y s b g hb
  refine ⟨s', R, t, ?_⟩
  intro i
  obtain ⟨H, hH⟩ := hh i
  exact ⟨{
    coefficient_boundary := ht i
    boundary_transport := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofFillerBoundaryHomotopy A D P x (y i) R (b i) (t i) (ht i)
    boundary_over :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofFillerBoundaryHomotopy_projection A D P x (y i) R (b i) (t i) (ht i)
    target_transport := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofSimplexRefinementHomotopy A D P x (y i) R (g i)
    target_over := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofSimplexRefinementHomotopy_projection A D P x (y i) R (g i)
    transport_boundary := fun h =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofFillerTransport_boundary A D P x (y i) R (b i) (g i) h (t i) (ht i)
    comparison := H
    comparison_over := hH }⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
