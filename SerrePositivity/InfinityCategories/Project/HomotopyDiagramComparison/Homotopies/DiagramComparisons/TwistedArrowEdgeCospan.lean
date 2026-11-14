module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.TwistedArrowEdgeCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection

/-!
概要：元の辺に付随する Tw 内の id_x → f ← id_y の同じ二辺を構成する。
方針：普遍的な二つの標準三単体を同じ元の辺へ後合成する。
規約：元の両恒等点と同じ終点を厳密に保持し、充填性を仮定しない。
使われ方：Yoneda の脚の恒等点像と反変輸送点を同じ点へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の辺自身を、Tw の同じ頂点として読む。 -/
def twistedArrowEdgeVertex {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C) _⦋0⦌ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).hom ≫ f

/-- 始点恒等射から元の辺への Tw 辺の元の一単体。 -/
def twistedArrowSourceEdgeSimplex {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C) _⦋1⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫
    stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom) ≫ f

/-- 終点恒等射から元の辺への Tw 辺の元の一単体。 -/
def twistedArrowTargetEdgeSimplex {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C) _⦋1⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫
    stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeOrderHom) ≫ f

/-- 定値の標準辺を元の辺へ写すと、同じ元の端点への定値写像になる。 -/
lemma twistedArrowConstantEdgeOrderHom_comp {C : SSet.{u}}
    (f : (Δ[1] : SSet.{u}) ⟶ C) (i : Fin 2) :
    stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowConstantEdgeOrderHom i)) ≫ f =
      SSet.const (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i)) := by
  have h : stdSimplex.map
      (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowConstantEdgeOrderHom i)) =
      (SSet.const (stdSimplex.obj₀Equiv.symm i) : (Δ[1] : SSet.{u}) ⟶ Δ[1]) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rw [h, SSet.const_comp]

/-- 始点側 Tw 辺は元の始点の恒等点を始点に持つ。 -/
lemma twistedArrowSourceEdgeSimplex_src {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C).δ 1 (twistedArrowSourceEdgeSimplex f) =
      SSet.const (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ 1) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫ stdSimplex.map
      (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom) ≫ f) = _
  have h := congrArg (fun g ↦ g ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdge_zero_face.{u})
  simpa only [Category.assoc, twistedArrowConstantEdgeOrderHom_comp, SSet.comp_const]
    using h

/-- 始点側 Tw 辺の終点は、同じ元の辺。 -/
lemma twistedArrowSourceEdgeSimplex_tgt {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C).δ 0 (twistedArrowSourceEdgeSimplex f) = twistedArrowEdgeVertex f := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ 0) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫ stdSimplex.map
      (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom) ≫ f) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).hom ≫ f
  have h := congrArg (fun g ↦ g ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdge_one_face.{u})
  have hi : stdSimplex.map (SimplexCategory.mkHom (OrderHom.id : Fin 2 →o Fin 2)) =
      (𝟙 (Δ[1] : SSet.{u})) := stdSimplex.map_id _
  simpa only [Category.assoc, hi, Category.id_comp] using h

/-- 終点側 Tw 辺は元の終点の恒等点を始点に持つ。 -/
lemma twistedArrowTargetEdgeSimplex_src {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C).δ 1 (twistedArrowTargetEdgeSimplex f) =
      SSet.const (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ 1) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫ stdSimplex.map
      (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeOrderHom) ≫ f) = _
  have h := congrArg (fun g ↦ g ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdge_zero_face.{u})
  simpa only [Category.assoc, twistedArrowConstantEdgeOrderHom_comp, SSet.comp_const]
    using h

/-- 終点側 Tw 辺の終点も、同じ元の辺。 -/
lemma twistedArrowTargetEdgeSimplex_tgt {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C).δ 0 (twistedArrowTargetEdgeSimplex f) = twistedArrowEdgeVertex f := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ 0) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫ stdSimplex.map
      (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeOrderHom) ≫ f) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).hom ≫ f
  have h := congrArg (fun g ↦ g ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdge_one_face.{u})
  have hi : stdSimplex.map (SimplexCategory.mkHom (OrderHom.id : Fin 2 →o Fin 2)) =
      (𝟙 (Δ[1] : SSet.{u})) := stdSimplex.map_id _
  simpa only [Category.assoc, hi, Category.id_comp] using h

/-- 元の始点の恒等点から元の辺への native な Tw 辺。 -/
def twistedArrowSourceEdge {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.Edge (SSet.const (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))
      (twistedArrowEdgeVertex f) :=
  ⟨twistedArrowSourceEdgeSimplex f, twistedArrowSourceEdgeSimplex_src f,
    twistedArrowSourceEdgeSimplex_tgt f⟩

/-- 元の終点の恒等点から同じ元の辺への native な Tw 辺。 -/
def twistedArrowTargetEdge {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.Edge (SSet.const (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)))
      (twistedArrowEdgeVertex f) :=
  ⟨twistedArrowTargetEdgeSimplex f, twistedArrowTargetEdgeSimplex_src f,
    twistedArrowTargetEdgeSimplex_tgt f⟩

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
