module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionEndpointEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionComparisonNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionHomotopyEdge

/-!
概要：底の図式の厳密な等式で、同じ初期図式を固定する延長空間を移す。
方針：等式による同型を使い、実際の延長・全族・終点評価を保持する。
規約：新しい持ち上げを選ばない。使われ方：左右の長辺を共通の根辺上で比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A D E B : SSet.{u}} (p : E ⟶ B) {β β' : A ⟶ B} (hβ : β = β')
  (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β) (hv' : v ≫ p = i ≫ β')

/-- 同じ底の二表示の間の固定延長空間の同型。 -/
def fixedExtensionBaseIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β' i v hv' := by
  subst β'
  exact Iso.refl _

/-- 底の表示を替えても、具体的な延長は同じ射である。 -/
lemma fixedExtensionBaseIso_vertex (W : A ⟶ E) (hW : W ≫ p = β) (hWi : i ≫ W = v) :
    (fixedExtensionBaseIso p hβ i v hv hv').hom.app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv ⟨W, hW, hWi⟩) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β' i v hv' ⟨W, hW.trans hβ, hWi⟩ := by
  subst β'
  rfl

/-- 任意のパラメータ族の展開は、底の表示によらず厳密に同じである。 -/
lemma fixedExtensionBaseIso_uncurry {T : SSet.{u}}
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (t ≫ (fixedExtensionBaseIso p hβ i v hv hv').hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β' i v hv') =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv) := by
  subst β'
  simp only [fixedExtensionBaseIso, Iso.refl_hom, Category.id_comp]

/-- 同じ終点での評価も、底の等式による移送と厳密に可換。 -/
lemma fixedExtensionBaseIso_endpoint {C : SSet.{u}} (j : C ⟶ A) (b : B _⦋0⦌)
    (hj : j ≫ β = SSet.const b) (hj' : j ≫ β' = SSet.const b) :
    (fixedExtensionBaseIso p hβ i v hv hv').hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint p β' i v hv' j b hj' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint p β i v hv j b hj := by
  subst β'
  simp only [fixedExtensionBaseIso, Iso.refl_hom, Category.id_comp]

/-- 同じ実際の円柱を表す辺も、等式による移送で選び直されない。 -/
lemma fixedExtensionBaseIso_homotopyEdge {W W' : A ⟶ E}
    (hW : W ≫ p = β) (hW' : W' ≫ p = β) (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (H : SSet.Homotopy W W') (hH : H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ β)
    (hI : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst D (Δ[1] : SSet.{u}) ≫ v) :
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge p β i v hv hW hW' hWi hWi' H hH hI).map
        (fixedExtensionBaseIso p hβ i v hv hv').hom).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge p β' i v hv' (hW.trans hβ) (hW'.trans hβ) hWi hWi'
        H (hH.trans (congrArg (fun b ↦ fst A (Δ[1] : SSet.{u}) ≫ b) hβ)) hI).edge := by
  subst β'
  rfl

/-- 可縮な延長空間の指定比較を、同じ二頂点の比較へ移す。 -/
lemma fixedExtensionBaseIso_vertexIso [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p β i hi v hv).vertexIso x y)
        (fixedExtensionBaseIso p hβ i v hv hv').hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p β' i hi v hv').vertexIso
        ((fixedExtensionBaseIso p hβ i v hv hv').hom.app _ x)
        ((fixedExtensionBaseIso p hβ i v hv hv').hom.app _ y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.contractibleVertexIso_map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p β i hi v hv)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p β' i hi v hv') _ x y

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
