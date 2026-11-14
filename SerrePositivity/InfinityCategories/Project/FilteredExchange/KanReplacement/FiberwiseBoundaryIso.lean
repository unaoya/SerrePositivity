module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberProductCofinality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ArrowBoundary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ArrowBoundaryEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ArrowBoundaryNaturality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace

/-!
概要：同じ底を共有する二点の関手の全空間は、元の全空間の fiber ごとの積。
方針：二点の内部 Hom の評価同型で底を変え、二項対角の引き戻し表示を使う。
規約：二つの元の射影を保持する。
使われ方：底を固定した path の両端評価の相対持ち上げ性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：二点の関手全空間の評価による、対角の引き戻しへの同型。
方針：境界評価の自然性と定値図式の対角表示を引き戻しに移す。
規約：底への射は恒等。使われ方：fiber ごとの積との比較の第一段。 -/
def fiberwiseBoundaryDiagonalIso {E B : SSet.{u}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary ≅ pullback (p ⊗ₘ p) (lift (𝟙 B) (𝟙 B)) :=
  asIso (pullback.map ((ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary B)
    (p ⊗ₘ p) (lift (𝟙 B) (𝟙 B)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowBoundaryEvaluationIso E).hom (𝟙 B)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowBoundaryEvaluationIso B).hom
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.arrowBoundaryEvaluation_naturality p).symm
    (by rw [Category.id_comp]; exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.constantDiagram_arrowBoundaryEvaluation B))

/-- 概要：底を共有する二点の関手全空間は、元の fiber ごとの積に厳密に同型。
方針：境界の評価と、元の二項対角の引き戻しの同型を合成する。
規約：元の二つの E。使われ方：path の元の両端の評価の標的。 -/
def fiberwiseBoundaryIso {E B : SSet.{u}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary ≅ pullback p p :=
  fiberwiseBoundaryDiagonalIso p ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberProduct_binaryDiagonal_isPullback p p).isoPullback.symm

/-- 概要：境界全空間の同型は元の二つの値の組を保持する。
方針：対角の引き戻し同型の第一射影と、境界の評価の第一射影を計算する。
規約：全パラメータで一致。使われ方：元の両端評価そのものへの持ち上げ性の輸送。 -/
lemma fiberwiseBoundaryIso_hom_product {E B : SSet.{u}} (p : E ⟶ B) :
    (fiberwiseBoundaryIso p).hom ≫ lift (pullback.fst p p) (pullback.snd p p) =
      pullback.fst ((ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary B) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluation E := by
  rw [fiberwiseBoundaryIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberProduct_binaryDiagonal_isPullback p p).isoPullback_inv_fst]
  change (fiberwiseBoundaryDiagonalIso p).hom ≫
    pullback.fst (p ⊗ₘ p) (lift (𝟙 _) (𝟙 _)) = _
  rw [fiberwiseBoundaryDiagonalIso, asIso_hom, pullback.map, pullback.lift_fst]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
