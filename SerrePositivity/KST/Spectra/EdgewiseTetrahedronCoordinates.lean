module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.OrdinalSimplexEdges
public import SerrePositivity.KST.Spectra.WeightedConeTriangleEdgewise
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightCoordinates

/-!
概要：edgewise 解像の一単体の左右の辺を、元の標準三単体の (0,1)・(2,3) 辺へ同定する。
方針：重みの標準単体同型の左右包含の式を使い、元の係数の射を後合成する。
規約：左辺の反転同型を相殺した向き。使われ方：錐比較の符号の三単体による計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EdgewiseCoordinates

/-- 左包含の標準三単体内での表示は、元の (0,1) 辺の Yoneda 射。 -/
lemma leftOrderMap :
    stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom 1 1)) =
      SSet.yonedaEquiv.symm (stdSimplex.edge.{u} 3 0 1 (by decide)) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 右包含の標準三単体内での表示は、元の (2,3) 辺の Yoneda 射。 -/
lemma rightOrderMap :
    stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1)) =
      SSet.yonedaEquiv.symm (stdSimplex.edge.{u} 3 2 3 (by decide)) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 元の edgewise の一単体を、元の Hom 内の標準三単体として読む射。 -/
def tetrahedronMap {X : SSet.{u}} (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋1⦌) :
    (Δ[3] : SSet.{u}) ⟶ X := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).inv ≫ a

/-- 左射影から読み取った元の経路は、この同じ三単体の (0,1) 辺。 -/
lemma leftCurve {X : SSet.{u}} (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋1⦌) :
    (stdSimplex.opIso ⦋1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}).op Δ[1] ≫ a =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 1 (by decide)) ≫ tetrahedronMap a := by
  calc
    _ = ((stdSimplex.opIso ⦋1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}).op Δ[1] ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).inv ≫ a := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_inl]
      simp only [Iso.inv_hom_id_assoc, leftOrderMap]
      rfl

/-- 右射影から読み取った元の経路は、この同じ三単体の (2,3) 辺。 -/
lemma rightCurve {X : SSet.{u}} (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}).op Δ[1] ≫ a =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 2 3 (by decide)) ≫ tetrahedronMap a := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}).op Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).inv ≫ a := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_inr, rightOrderMap]
      rfl

/-- 解像の零面は、元の三単体の外側の (0,3) 辺を残す。 -/
lemma zeroFaceOrderMap :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ (0 : Fin 2)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 3 (by decide)) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> decide

/-- 解像の一面は、元の三単体の内側の (1,2) 辺を残す。 -/
lemma oneFaceOrderMap :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ (1 : Fin 2)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 1 2 (by decide)) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> decide

/-- 解像の頂点を、元の Hom 内の辺として読む同じ重みの標準表示。 -/
def vertexMap {X : SSet.{u}} (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⟶ X := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).inv ≫ b

/-- 解像の一単体の終点は、元の三単体の同じ外辺 (0,3)。 -/
lemma zeroFace {X : SSet.{u}} (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋1⦌) :
    vertexMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X).δ 0 a) =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 3 (by decide)) ≫ tetrahedronMap a := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ 0) ≫ a) = _
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ 0) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).inv ≫ a := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [zeroFaceOrderMap]; rfl

/-- 解像の一単体の始点は、元の三単体の同じ内辺 (1,2)。 -/
lemma oneFace {X : SSet.{u}} (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋1⦌) :
    vertexMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X).δ 1 a) =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 1 2 (by decide)) ≫ tetrahedronMap a := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ 1) ≫ a) = _
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ 1) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).inv ≫ a := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [oneFaceOrderMap]; rfl

end SerrePositivity.KST.Spectra.EdgewiseCoordinates
