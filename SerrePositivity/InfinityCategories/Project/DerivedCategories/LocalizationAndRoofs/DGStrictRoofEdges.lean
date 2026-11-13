module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGStrictRoofVertices

/-! # 指定閉細分と閉分子の実屋根の辺

概要：元の厳密閉細分射と閉分子から、指定両端を持つ実屋根の辺を構成する。
方針：厳密屋根圏の指定射の nerve 辺を写し、分母・分子の二射影を計算する。
規約：実際の一単体と全端点を保持する。使われ方：有限相対充填の共通細分の実辺化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

/-- 通常の圏の指定射を、元の指定零単体を両端とする実 nerve 辺として読む。 -/
def roofNerveEdge {C : Type v} [Category.{u} C] {c d : C} (r : c ⟶ d) :
    (nerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d) :=
  SSet.Edge.mk (ComposableArrows.mk₁ r) (ComposableArrows.ext₀ rfl)
    (ComposableArrows.ext₀ rfl)

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 指定された閉細分と閉分子の前合成を、元の実屋根の指定辺にする。 -/
def dgStrictRoofRefinementEdge (P : Set D) (x y : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : t.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y).Edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofVertex A D P x y s (r.hom.left ≫ f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofVertex A D P x y t f) :=
  (roofNerveEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofRefine A D P x y r f)).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofNerveMap A D P x y)

/-- 実細分辺の分母成分は、元の指定細分射の実 over 辺。 -/
lemma dgStrictRoofRefinementEdge_projection (P : Set D) (x y : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : t.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y).app (Opposite.op ⦋1⦌)
      (dgStrictRoofRefinementEdge A D P x y r f).edge =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ r) := by
  have h := congrArg (fun F => F.app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofRefine A D P x y r f)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofNerveMap_projection A D P x y)
  refine h.trans ?_
  exact congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋1⦌) z)
    (nerveMap_app_mk₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofDenominator A D P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofRefine A D P x y r f))

/-- 実細分辺の分子成分は、元の閉射の厳密な前合成三角形の実 slice 辺。 -/
lemma dgStrictRoofRefinementEdge_target (P : Set D) (x y : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : t.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y).app (Opposite.op ⦋1⦌)
      (dgStrictRoofRefinementEdge A D P x y r f).edge =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A D y).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ (Over.homMk r.hom.left rfl : Over.mk (r.hom.left ≫ f) ⟶
        Over.mk f)) := by
  have h := congrArg (fun F => F.app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofRefine A D P x y r f)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofNerveMap_target A D P x y)
  refine h.trans ?_
  exact congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A D y).app (Opposite.op ⦋1⦌) z)
    (nerveMap_app_mk₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofNumerator A D P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofRefine A D P x y r f))

/-- 実細分辺の元の始域成分は、指定閉細分射の実閉辺そのもの。 -/
lemma dgStrictRoofRefinementEdge_source (P : Set D) (x y : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : t.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y).app (Opposite.op ⦋1⦌)
        (dgStrictRoofRefinementEdge A D P x y r f).edge) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.hom.left).edge := by
  rw [dgStrictRoofRefinementEdge_projection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_edge_source]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
