module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.MapTransportCylinder
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PrismTransportPointEvaluation

/-!
概要：標準 prism の底上の像に対する輸送比較を、既存の輸送自然性と照合する。
方針：同じ比較円柱の終点の類を二通りに計算し、その一点制限も評価する。
規約：同じ底の辺と元の射を保持する。使われ方：左三角形の実際の成分の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
  (r : E ⟶ E') (hr : r ≫ q = p) {a b : B _⦋0⦌} (e : B.Edge a b)
local notation "F₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr a
local notation "F₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr b

/-- 元の標準 prism の像に対する輸送比較は、既存の輸送自然性の射と一致する。 -/
lemma mapTransportPrism_transportIso_hom :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso q e F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ F₁)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism p r e) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_zero p q r hr e)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_one p q r hr e) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_projection p q r hr e)).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso p q r hr e).hom := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportEndpointHomotopy_hom q e F₀ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism p r e)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_zero p q r hr e) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_projection p q r hr e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ F₁) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_one p q r hr e)).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportEndpointHomotopy_hom p q r hr e)

/-- 一点で同じ標準 prism の像となる全族の比較成分は、元の輸送自然性の点評価。 -/
lemma prismTransportComponent_map_hom_arrow {A : SSet.{u}}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q a) (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E')
    (hH₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q a)
    (hH₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b)
    (hHp : H ≫ q = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
    (x : A _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp H (SSet.yonedaEquiv.symm x) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism p r e) (SSet.yonedaEquiv.symm v)) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso q e f g H hH₀ hH₁ hHp).toNatIso.hom.app
      (SSet.HomotopyCategory.mk x)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso p q r hr e)
          (SSet.yonedaEquiv.symm v)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b)).hom).hom := by
  refine (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportComponent_hom_arrow q e f g H hH₀ hH₁ hHp x).trans ?_
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso q e (SSet.yonedaEquiv.symm x ≫ f)
    (SSet.yonedaEquiv.symm x ≫ g) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp H (SSet.yonedaEquiv.symm x))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_zero q f H hH₀ (SSet.yonedaEquiv.symm x))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_one q H (SSet.yonedaEquiv.symm x) g hH₁)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_projection q e H hHp (SSet.yonedaEquiv.symm x))
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso p q r hr e)
    (SSet.yonedaEquiv.symm v)
  have hh : Arrow.mk Q.hom = Arrow.mk R.hom := by
    refine (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportIso_raw_hom_arrow q e
      (SSet.yonedaEquiv.symm x ≫ f) (SSet.yonedaEquiv.symm x ≫ g)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp H (SSet.yonedaEquiv.symm x))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism p r e) (SSet.yonedaEquiv.symm v))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_zero q f H hH₀ (SSet.yonedaEquiv.symm x))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_one q H (SSet.yonedaEquiv.symm x) g hH₁)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_projection q e H hHp (SSet.yonedaEquiv.symm x))
      (SSet.yonedaEquiv.symm v ≫ F₀) (SSet.yonedaEquiv.symm v ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ F₁))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_zero q F₀ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism p r e)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_zero p q r hr e) (SSet.yonedaEquiv.symm v))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_one q (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism p r e) (SSet.yonedaEquiv.symm v)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ F₁) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_one p q r hr e))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_projection q e (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism p r e)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_projection p q r hr e) (SSet.yonedaEquiv.symm v)) hx).trans ?_
    refine (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportIso_parameter_hom_arrow q e F₀ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism p r e)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_zero p q r hr e) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_projection p q r hr e)
      (SSet.yonedaEquiv.symm v) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ F₁)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism_one p q r hr e)).trans ?_
    exact congrArg
      (hoFunctor.map ((pre (SSet.yonedaEquiv.symm v)).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b))).toFunctor.mapArrow.obj
      (congrArg Arrow.mk (mapTransportPrism_transportIso_hom p q r hr e))
  exact congrArg
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b)).hom).toFunctor.mapArrow.obj hh

/-- 点での自然性同型の両端表示を変えても、全族の同じ比較成分を回収する。 -/
lemma prismTransportComponent_map_pointIso_hom_arrow {A : SSet.{u}}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q a) (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E')
    (hH₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q a)
    (hH₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b)
    (hHp : H ≫ q = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
    (x : A _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp H (SSet.yonedaEquiv.symm x) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism p r e) (SSet.yonedaEquiv.symm v))
    {U V : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b} (J : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso U V)
    (hJ : Arrow.mk J.hom = Arrow.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso p q r hr e)
        (SSet.yonedaEquiv.symm v)).hom) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso q e f g H hH₀ hH₁ hHp).toNatIso.hom.app
      (SSet.HomotopyCategory.mk x)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map J (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b)).hom).hom := by
  refine (prismTransportComponent_map_hom_arrow p q r hr e f g H hH₀ hH₁ hHp x v hx).trans ?_
  exact congrArg
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b)).hom).toFunctor.mapArrow.obj hJ.symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
