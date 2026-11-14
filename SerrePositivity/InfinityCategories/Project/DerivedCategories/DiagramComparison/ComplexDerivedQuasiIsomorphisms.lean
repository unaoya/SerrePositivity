module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedEdges

/-!
概要：元の複体の実評価を、同じ擬同型辺の反転へ接続する。
方針：一点加群での評価が元の鎖写像を保つことを確認し、指定分解の反転性を使う。
規約：元の閉射・分解・評価を保持する。
使われ方：3b-3 R5、strict図式の評価の局所化への因子化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A]

/-- 元の鎖写像を閉零射・一点加群として読み評価すると、同じ鎖写像を回収する。 -/
lemma complexClosedPresentation_ring_evaluation {X Y : Complex A} (f : X ⟶ Y) :
    (moduleEvaluation A PUnit.{1} PUnit.unit).map
      ((ringConstantDG A).onClosed.map ((complexClosedPresentation A).map f)) = f := by
  change (complexClosedHomEquiv A X Y)
    (ForgetEnrichment.homOf (Complex A)
      ((ForgetEnrichment.homTo (Complex A) ((complexClosedPresentation A).map f) ≫
        (ringConstantHomIso A X Y).inv) ≫ (ringConstantHomIso A X Y).hom)) = f
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, ForgetEnrichment.homOf_homTo]
  exact Equiv.apply_symm_apply _ _

/-- 元の擬同型は、一点加群の元の閉射としてもobjectwise擬同型。 -/
lemma complexClosedPresentation_moduleQuasiIso {X Y : Complex A} (f : X ⟶ Y) [QuasiIso f] :
    moduleQuasiIso A PUnit.{1}
      ((ringConstantDG A).onClosed.map ((complexClosedPresentation A).map f)) := by
  rw [moduleQuasiIso_iff]
  rintro ⟨⟩
  rw [complexClosedPresentation_ring_evaluation]
  infer_instance

/-- 元の閉零射のnerve辺は、元の鎖写像のdg辺そのもの。 -/
lemma complexClosedPresentation_nerve_edge {X Y : Complex A} (f : X ⟶ Y) :
    (nerveMap (complexClosedPresentation A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app
      (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      (dgClosedEdge A (Complex A) ((complexClosedPresentation A).map f)).edge := by
  apply (dgNerve.edgeEquiv A (Complex A)).injective
  change dgNerve.edgeEquiv A (Complex A)
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app _
      ((nerveMap (complexClosedPresentation A)).app _ (ComposableArrows.mk₁ f))) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_edge]
  change _ = Simplex.edgeEquiv
    ((Simplex.edgeEquiv (A := A) (D := Complex A)).symm
      ⟨pairObj X Y, closedHomEquiv A (Complex A) _ _ ((complexClosedPresentation A).map f)⟩)
  rw [Equiv.apply_symm_apply]
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    rfl

/-- 元の複体から既存D(A)への指定実評価は、元の擬同型辺を反転する。 -/
lemma complexDerivedEvaluation_inverts_quasiIso {X Y : Complex A} (f : X ⟶ Y) [QuasiIso f] :
    IsInvertibleEdge (edgeOfSimplex ((complexDerivedEvaluation A).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ f))) := by
  have h := dgModuleResolvedInfinity_invertsQuasiIso A (Complex A) PUnit.{1} (ringConstantDG A)
    (dgClosedEdge A (Complex A) ((complexClosedPresentation A).map f))
    (by rw [dgClosedEdge_closed]; exact complexClosedPresentation_moduleQuasiIso A f)
  have h' := h.map (semifreePointEquivalence A).hom
  apply (isInvertibleEdge_congr (e := edgeOfSimplex ((complexDerivedEvaluation A).app
    (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f))) (f := _) ?_).mpr h'
  change ((dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
    (semifreePointEquivalence A).hom).app (Opposite.op ⦋1⦌))
      ((nerveMap (complexClosedPresentation A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ f)) = _
  rw [complexClosedPresentation_nerve_edge]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
