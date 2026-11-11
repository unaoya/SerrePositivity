module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionBaseIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionVertexEvaluation

/-!
概要：全延長の終点評価を、底の等式と形状の制限に対して自然にする。
方針：任意の族の評価を raw な展開の頂点制限として計算する。
規約：終点 fiber の同型を選ばず、同じ射の等式で比較する。
使われ方：共通長辺上の終点と、元の三角形の終端辺上の終点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 任意のパラメータ族の終点評価は、同じ raw な族の指定頂点での制限。 -/
lemma fixedExtensionEdgeTarget_parameter {K D E B T : SSet.{u}}
    (p : E ⟶ B) (β : K ⟶ B) (i : D ⟶ K) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (k : (Δ[1] : SSet.{u}) ⟶ K) {a b : B _⦋0⦌} (e : B.Edge a b)
    (hk : k ≫ β = SSet.yonedaEquiv.symm e.edge)
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv) :
    t ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      lift (SSet.const (k.app _ (stdSimplex.obj₀Equiv.symm 1))) (𝟙 T) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_evaluate]
  simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_at_vertex p β
    (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv)
    (k.app _ (stdSimplex.obj₀Equiv.symm 1))

/-- 同じ終点頂点を持つ二つの辺での評価は、同じ fiber 内の射である。 -/
lemma fixedExtensionEdgeTarget_eq_of_vertex {K D E B : SSet.{u}}
    (p : E ⟶ B) (β : K ⟶ B) (i : D ⟶ K) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (k l : (Δ[1] : SSet.{u}) ⟶ K) {a a' b : B _⦋0⦌}
    (e : B.Edge a b) (e' : B.Edge a' b)
    (hk : k ≫ β = SSet.yonedaEquiv.symm e.edge)
    (hl : l ≫ β = SSet.yonedaEquiv.symm e'.edge)
    (h : k.app _ (stdSimplex.obj₀Equiv.symm 1) = l.app _ (stdSimplex.obj₀Equiv.symm 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv l e' hl := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_evaluate, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_evaluate, h]

/-- 底の表示の移送は、同じ指定辺の終点評価を保つ。 -/
lemma fixedExtensionBaseIso_edgeTarget {K D E B : SSet.{u}}
    (p : E ⟶ B) {β β' : K ⟶ B} (hβ : β = β')
    (i : D ⟶ K) (v : D ⟶ E) (hv : v ≫ p = i ≫ β) (hv' : v ≫ p = i ≫ β')
    (k : (Δ[1] : SSet.{u}) ⟶ K) {a b : B _⦋0⦌} (e : B.Edge a b)
    (hk : k ≫ β = SSet.yonedaEquiv.symm e.edge)
    (hk' : k ≫ β' = SSet.yonedaEquiv.symm e.edge) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso p hβ i v hv hv').hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β' i v hv' k e hk' =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk := by
  subst β'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso, Iso.refl_hom, Category.id_comp]

/-- 制限してから同じ終点を評価しても、元の全延長の終点評価になる。 -/
lemma fixedExtensionRestriction_edgeTarget {K L D E B : SSet.{u}}
    (p : E ⟶ B) (β : K ⟶ B) (k : L ⟶ K) (j : D ⟶ L)
    (v : D ⟶ E) (hv : v ≫ p = (j ≫ k) ≫ β) (l : (Δ[1] : SSet.{u}) ⟶ L)
    {a b : B _⦋0⦌} (e : B.Edge a b) (hl : l ≫ (k ≫ β) = SSet.yonedaEquiv.symm e.edge) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction p β k j v hv ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p (k ≫ β) j v (hv.trans (Category.assoc _ _ _)) l e hl =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β (j ≫ k) v hv (l ≫ k) e
        ((Category.assoc _ _ _).trans hl) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [Category.assoc, fixedExtensionEdgeTarget_parameter]
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β (j ≫ k) v hv
  have hU := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_uncurry p β k j v hv (𝟙 S)
  simp only [Category.id_comp] at hU
  have hR := fixedExtensionEdgeTarget_parameter p β (j ≫ k) v hv (l ≫ k) e
    ((Category.assoc _ _ _).trans hl) (𝟙 S)
  simp only [Category.id_comp] at hR
  rw [hU, hR, ← Category.assoc, lift_whiskerRight, SSet.const_comp]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
