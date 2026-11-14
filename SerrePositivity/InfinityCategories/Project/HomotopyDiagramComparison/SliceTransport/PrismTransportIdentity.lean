module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PrismCylinderEndpoint
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：標準 prism 自身を入力した輸送比較同型は、同じ終点族の恒等同型となる。
方針：底と初期値を保つ定値円柱を明示し、その終点比較の類を既存の同型へ移す。
規約：単に両端が同じという理由では同型を恒等としない。使われ方：三角形比較の標準側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b : B _⦋0⦌} (e : B.Edge a b) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)

/-- 標準 prism 自身の、底と初期値を固定する定値の比較円柱。 -/
def prismTransportIdentityCylinder :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismTransportCylinder p e f (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f) where
  homotopy := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f)
  projection := by
    change (fst _ (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f) ≫ p = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_projection]
  initial := by
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ A) ▷ (Δ[1] : SSet.{u})) ≫
      (fst _ (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f) = _
    have h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f =
        snd (Δ[0] : SSet.{u}) A ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_zero]
    rw [← Category.assoc, whiskerRight_fst, Category.assoc, h₀]

/-- 定値比較円柱の終点も、同じ終点族の定値円柱の raw な射である。 -/
lemma prismTransportIdentityEndpoint_raw :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy p e f (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f)
      (prismTransportIdentityCylinder p e f) (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_one p e f)).h =
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e)).h := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy_projection]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫
      (fst _ (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f) =
    (fst _ (Δ[1] : SSet.{u}) ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
  rw [← Category.assoc, whiskerRight_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_one]
  simp only [Category.assoc]

/-- 標準 prism の輸送比較同型の射は、明示した定値円柱により恒等射と一致する。 -/
lemma prismTransportIso_standard_hom :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso p e f (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_zero p e f)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_one p e f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_projection p e f)).hom =
        𝟙 (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy_hom p e f (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_zero p e f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_projection p e f)
    (prismTransportIdentityCylinder p e f) (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_one p e f)
  apply Arrow.mk_injective _ _
  refine (congrArg Arrow.mk h).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq _ _ (prismTransportIdentityEndpoint_raw p e f)).trans ?_)
  exact congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e))

/-- 標準 prism 自身の比較は、同じ終点図式の恒等同型である。 -/
lemma prismTransportIso_standard :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso p e f (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_zero p e f)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_one p e f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_projection p e f) =
        Iso.refl (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e))) := by
  apply Iso.ext
  exact prismTransportIso_standard_hom p e f

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
