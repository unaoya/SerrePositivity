module

public import SerrePositivity.InfinityCategories.HTT.Section2_4_1.CartesianComparisonBoundary
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.CartesianHomotopyExtension

/-!
概要：同じ終点を持つ二つの輸送 prism の比較正方形を構成する。
方針：二側面を指定した Cartesian 相対延長を適用し、始点側の境界と底を回収する。
規約：指定した右の輸送を変えない。使われ方：元の下段 cf nerve 上の単位の候補。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 元の二側面・終点・底を固定した Cartesian な比較正方形を構成する。 -/
lemma exists_cartesianPrismComparison {A E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p]
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hH : H ≫ p = fst (Δ[1] : SSet.{u}) A)
    (hK : K ≫ p = fst (Δ[1] : SSet.{u}) A)
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H)
    (hKc : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p
      (K.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) :
    ∃ J : (Δ[1] : SSet.{u}) ⊗ ((Δ[1] : SSet.{u}) ⊗ A) ⟶ E,
      ((Δ[1] : SSet.{u}) ◁ ((boundary 1).ι ▷ A)) ≫ J = _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary H K ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ J = H ∧
      J ≫ p = ((Δ[1] : SSet.{u}) ◁ fst (Δ[1] : SSet.{u}) A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction 1 ∧
      ∀ x : ((Δ[1] : SSet.{u}) ⊗ A) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p
        (J.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  have hi : Mono ((boundary 1).ι ▷ A) := by
    have happ : ∀ d, Mono (((boundary 1).ι ▷ A).app d) := by
      intro d
      apply (mono_iff_injective _).mpr
      rintro ⟨s, x⟩ ⟨t, y⟩ h
      change (s.val, x) = (t.val, y) at h
      have hs : s.val = t.val := congrArg
        (fun z : (Δ[1] : SSet.{u}).obj d × A.obj d ↦ z.1) h
      have hx : x = y := congrArg
        (fun z : (Δ[1] : SSet.{u}).obj d × A.obj d ↦ z.2) h
      exact Prod.ext (Subtype.ext hs) hx
    exact NatTrans.mono_of_mono_app _
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianHomotopy_extend p ((boundary 1).ι ▷ A) (_root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary H K) H
  · exact _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary_target H K h1
  · rw [hH, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction_one, Category.comp_id]
  · exact _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary_base p H K hH hK
  · exact _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary_vertical p H K hKc

/-- 比較正方形の始点側の両端は、元の二つの輸送の始点である。 -/
lemma cartesianPrismComparison_unit_boundary {A E : SSet.{u}}
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (J : (Δ[1] : SSet.{u}) ⊗ ((Δ[1] : SSet.{u}) ⊗ A) ⟶ E)
    (hJ : ((Δ[1] : SSet.{u}) ◁ ((boundary 1).ι ▷ A)) ≫ J =
      _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary H K) :
    ((boundary 1).ι ▷ A) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ J) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ K) := by
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hJ,
    _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary_source]

/-- 比較正方形の始点側は、底の零頂点の上にある。 -/
lemma cartesianPrismComparison_unit_base {A E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (J : (Δ[1] : SSet.{u}) ⊗ ((Δ[1] : SSet.{u}) ⊗ A) ⟶ E)
    (hJ : J ≫ p = ((Δ[1] : SSet.{u}) ◁ fst (Δ[1] : SSet.{u}) A) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ J) ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [Category.assoc, hJ, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction_zero, SSet.comp_const]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
