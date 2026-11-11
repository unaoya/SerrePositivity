module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentPointHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInitialSpan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeSectionFiber

/-!
概要：底の同じ頂点の表示変更と、初期 Hom の点図式表示の同型の両立を証明する。
方針：任意の点図式の Yoneda 表示で先に相殺し、元の base 同型の定義へ代入する。
規約：上の図式や始点が異なっても使える。使われ方：native と指定余錐の Hom パラメータ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 点図式の二表示の間の移送は、同じ pinched Hom と coslice fiber の同型と両立する。 -/
lemma pointHomPresentation_inv_transport {X : SSet.{u}} {a b : (Δ[0] : SSet.{u}) ⟶ X}
    {x x' : X _⦋0⦌} (ha : a = SSet.yonedaEquiv.symm x) (hb : b = SSet.yonedaEquiv.symm x')
    (h : x = x') (y : X _⦋0⦌) :
    eqToHom (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft z y) h) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso x' y).hom ≫
          eqToHom (congrArg (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace s y) hb.symm) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso x y).hom ≫
        eqToHom (congrArg (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace s y) ha.symm)) ≫
          eqToHom (congrArg (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace s y)
            (ha.trans ((congrArg SSet.yonedaEquiv.symm h).trans hb.symm))) := by
  subst x' a b
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 異なる上の図式・始点の base 同型も、同じ底の頂点の表示変更と厳密に両立する。 -/
lemma initialBaseIso_inv_vertexTransport {E F X : SSet.{u}} (p : E ⟶ X) (q : F ⟶ X)
    (c : E _⦋0⦌) (d : F _⦋0⦌)
    (h : p.app (Opposite.op ⦋0⦌) c = q.app (Opposite.op ⦋0⦌) d) (y : X _⦋0⦌) :
    eqToHom (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft z y) h) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q d y).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso p c y).inv ≫
        eqToHom (congrArg (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace s y)
          ((SSet.yonedaEquiv_symm_comp c p).trans
            ((congrArg SSet.yonedaEquiv.symm h).trans (SSet.yonedaEquiv_symm_comp d q).symm))) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
    Category.assoc] using pointHomPresentation_inv_transport
      (SSet.yonedaEquiv_symm_comp c p) (SSet.yonedaEquiv_symm_comp d q) h y

/-- 同じ頂点を持つ二つの余錐の点図式表示は、同じ頂点の等式から厳密に移送される。 -/
lemma coconeVertexDiagram_of_vertex_eq {K L X : SSet.{u}} {p : K ⟶ X} {q : L ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (h : c.vertex = d.vertex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram c = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram_eq c).trans
    ((congrArg SSet.yonedaEquiv.symm h).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram_eq d).symm)

/-- 制限の標的図式の表示変更は、同じ正規化制限の後の fiber 表示変更そのものである。 -/
lemma normalizedCoconeRestrictionFiber_targetEq {K L X : SSet.{u}} (p : K ⟶ X)
    (i : L ⟶ K) (a b : L ⟶ X) (ha : i ≫ p = a) (hb : i ≫ p = b)
    (h : a = b) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber p i hb y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber p i ha y ≫
        eqToHom (congrArg (fun d ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace d y) h) := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
