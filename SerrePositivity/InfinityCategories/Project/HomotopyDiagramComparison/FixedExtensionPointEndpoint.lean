module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionRelativeEndpoint
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionVertexEvaluation

/-!
概要：固定初期値の終点制限を、同じ終点 fiber への評価として同定する。
方針：一点上の相対関手の評価同型と、底の点の等式による移送を使う。
規約：全延長の同じ射を保持する。使われ方：既存の根辺終点評価の left fibration 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma vertexFiber_eqToHom_ι {E B : SSet.{u}} (p : E ⟶ B) {a b : B _⦋0⦌}
    (h : a = b) : eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a := by
  subst b
  simp only [eqToHom_refl, Category.id_comp]

/-- 定値な一点図式の値は、同じ指定した底の頂点。 -/
lemma pointDiagramValue_of_constant {B : SSet.{u}} (β : (Δ[0] : SSet.{u}) ⟶ B)
    (b : B _⦋0⦌) (h : β = SSet.const b) :
    β.app _ (stdSimplex.obj₀Equiv.symm 0) = b := by
  rw [h]
  simp [SSet.const]

variable {A D E B : SSet.{u}} (p : E ⟶ B) (β : A ⟶ B)
  (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
  (j : (Δ[0] : SSet.{u}) ⟶ A) (b : B _⦋0⦌) (hj : j ≫ β = SSet.const b)

/-- 同じ一点終点での制限を、指定した底の fiber へ評価する。 -/
def fixedExtensionPointEndpoint : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRelativeEndpoint p β i v hv j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativePointFunctorIso p (j ≫ β)).hom ≫
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) (pointDiagramValue_of_constant (j ≫ β) b hj))

/-- 結合した包含が単射なら、この終点評価は left fibration。 -/
instance fixedExtensionPointEndpoint_leftFibration [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [Mono (coprod.desc i j)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (fixedExtensionPointEndpoint p β i v hv j b hj) := by
  dsimp only [fixedExtensionPointEndpoint]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRelativeEndpoint p β i v hv j))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.of_isIso _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.of_isIso _))⟩

/-- 終点評価の包含は、元の全族の同じ頂点での評価そのもの。 -/
lemma fixedExtensionPointEndpoint_ι :
    fixedExtensionPointEndpoint p β i v hv j b hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex β) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (j.app _ (stdSimplex.obj₀Equiv.symm 0)) := by
  dsimp only [fixedExtensionPointEndpoint]
  rw [Category.assoc, Category.assoc,
    vertexFiber_eqToHom_ι p (pointDiagramValue_of_constant (j ≫ β) b hj)]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRelativeEndpoint]
  rw [Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv),
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β j), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_point_evaluate]
  exact congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv ≫ t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_ι p β (j.app _ (stdSimplex.obj₀Equiv.symm 0)))

variable (k : (Δ[1] : SSet.{u}) ⟶ A) {a : B _⦋0⦌} (e : B.Edge a b)
  (hk : k ≫ β = SSet.yonedaEquiv.symm e.edge)

omit j hj in
include hk in
/-- 同じ辺の終端点は、底の同じ指定終点に定値である。 -/
lemma fixedExtensionEdgeTarget_point_base :
    (stdSimplex.δ (0 : Fin 2) ≫ k) ≫ β = SSet.const b :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ stdSimplex.δ (0 : Fin 2) ≫ z) hk).trans
      ((e).δ_zero_yonedaEquiv_symm.trans (SSet.yonedaEquiv_symm_zero b)))

omit j hj in
/-- 既存の全辺の終点評価は、同じ一点の相対評価と厳密に一致する。 -/
lemma fixedExtensionEdgeTarget_eq_pointEndpoint :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk =
      fixedExtensionPointEndpoint p β i v hv (stdSimplex.δ (0 : Fin 2) ≫ k) b
        (fixedExtensionEdgeTarget_point_base β b k e hk) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_evaluate, fixedExtensionPointEndpoint_ι]
  rfl

omit j hj in
/-- 終端点と初期包含の余積が単射なら、既存の全辺の終点評価は left fibration。 -/
instance fixedExtensionEdgeTarget_leftFibration [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    [Mono (coprod.desc i (stdSimplex.δ (0 : Fin 2) ≫ k))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk) := by
  rw [fixedExtensionEdgeTarget_eq_pointEndpoint p β i v hv b k e hk]
  infer_instance

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
