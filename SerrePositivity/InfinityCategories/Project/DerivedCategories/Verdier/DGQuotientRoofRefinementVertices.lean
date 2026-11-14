module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientRoofRefinementFillers

/-! # 指定済み屋根の有限商頂点を共通細分後で持ち上げる

概要：零次元の指定商頂点の有限族も、既存屋根への共通細分後で元の屋根の像へ結ぶ。
方針：零単体には真の非空部分集合が無いことを使い、全次元の相対比較へ適用する。
規約：既存屋根と全指定商頂点を保持する。使われ方：屋根比較の充填判定の基底。
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

/-- 任意の有限商頂点を、指定済み屋根への一つの共通細分後で元の頂点の像へ結ぶ。 -/
theorem dgQuotientRoofRefinement_vertex_lifts (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m : ℕ} (x : D) (y : Fin m → D) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (g : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))) _⦋0⦌) :
    ∃ s' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x, ∃ _r : s' ⟶ s,
      ∃ t : ∀ i, ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierRoofDiagram A D P x (y i)).obj (op s')) _⦋0⦌,
        ∀ i, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofConstantComparison A D P x (y i)).app (op s'))
          (SSet.yonedaEquiv.symm (t i) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofComparison A D P x (y i)).app (op s'))) := by
  let q := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left
  let g' := fun i => ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofConstantComparison A D P x (y i)).app (op s)).app
    (Opposite.op ⦋0⦌) (g i)
  have hfull (J : Finset (Fin 1)) (hJ : J.Nonempty) : J = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    obtain ⟨a, ha⟩ := hJ
    exact (Subsingleton.elim a j) ▸ ha
  obtain ⟨p, r, hr, t, _, hh⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_pinchedRelativeHomotopies A D P hP
    q y (fun _ => 0) (fun _ J _ hJ _ hne => (hne (hfull J hJ)).elim)
    (fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (g' i)) (fun _ J _ hJ _ hne => (hne (hfull J hJ)).elim)
  let s' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefine A D P x s r hr
  refine ⟨s', _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefineHom A D P x s r hr, fun i => (t i).toPinched, ?_⟩
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
