module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionEdgeFamily

/-!
概要：底上の関手による fiber の写像と、実際の比較辺による Hom 比較の自然性を証明する。
方針：始対象の族の像に底の辺の合成三角形の切断を適用し、固定終点の Hom 比較と結ぶ。
規約：比較辺は全空間の実際の辺。写像空間への単体的ホモトピーそのものを構成する。
使われ方：余錐の制限と部分余極限頂点の比較射の、全 Hom パラメータでの照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B)
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex d)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)

/-- 元の族の像を、底の実際の比較辺を含む合成三角形の族に延長する。 -/
def initialRestrictionBaseTriangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm e.edge ≫ q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily p q r hr d hd e y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) q ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection (SSet.yonedaEquiv.symm e.edge ≫ q)

/-- 底の合成三角形の族は、指定した終点側の族を厳密に保つ。 -/
lemma initialRestrictionBaseTriangle_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily p q r hr d hd e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) q =
      initialRestrictionBaseTriangle p q r hr d hd e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (SSet.yonedaEquiv.symm e.edge ≫ q) (stdSimplex.δ (0 : Fin 2)) := by
  simp only [initialRestrictionBaseTriangle, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection_target]
  erw [Category.comp_id]

/-- 比較辺による合成三角形の始点側を、実際の左 pinched Hom へ移す。 -/
def initialRestrictionEdgeHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (q.app (Opposite.op ⦋0⦌) c) y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeBaseSource q c (SSet.yonedaEquiv.symm e.edge) e.δ_one_yonedaEquiv_symm y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily p q r hr d hd e y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily_fixed p q r hr d hd e y)
    (initialRestrictionBaseTriangle p q r hr d hd e y)
    (initialRestrictionBaseTriangle_target p q r hr d hd e y) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom

/-- 底上の関手の fiber の作用と比較辺の合成三角形による Hom の作用は、全単体でホモトピック。 -/
lemma initialRestrictionHomComparison_homotopy [InnerFibration q] (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c) :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison q c hc y)
      (initialRestrictionEdgeHomFamily p q r hr d hd e y)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomComparison_edge_family_pinched_homotopy q c
    (SSet.yonedaEquiv.symm e.edge) e.δ_one_yonedaEquiv_symm y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily p q r hr d hd e y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily_fixed p q r hr d hd e y)
    (initialRestrictionBaseTriangle p q r hr d hd e y)
    (initialRestrictionBaseTriangle_target p q r hr d hd e y) hc
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily_vertexFiberLift] at H
  exact H

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
