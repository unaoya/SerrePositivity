module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGStrictMappedRoofVertices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGStrictRoofEdges

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

variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 指定された閉細分と閉分子の前合成を、元の実屋根の指定辺にする。 -/
def dgStrictMappedRoofRefinementEdge (P : Set D) (x : D) (y : E)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : F.onClosed.obj t.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappedRoofCorrespondence A D E F P x y).Edge
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofVertex A D E F P x y s (F.onClosed.map r.hom.left ≫ f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofVertex A D E F P x y t f) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofNerveEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofRefine A D E F P x y r f)).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofNerveMap A D E F P x y)

/-- 実細分辺の分母成分は、元の指定細分射の実 over 辺。 -/
lemma dgStrictMappedRoofRefinementEdge_projection (P : Set D) (x : D) (y : E)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : F.onClosed.obj t.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (pullback.snd _ _ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappedRoofCorrespondence A D E F P x y ⟶ _).app (Opposite.op ⦋1⦌)
      (dgStrictMappedRoofRefinementEdge A D E F P x y r f).edge =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ r) := by
  have h := congrArg (fun G => G.app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofRefine A D E F P x y r f)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofNerveMap_projection A D E F P x y)
  refine h.trans ?_
  exact congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋1⦌) z)
    (nerveMap_app_mk₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofDenominator A D E F P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofRefine A D E F P x y r f))

/-- 実細分辺の分子成分は、元の閉射の厳密な前合成三角形の実 slice 辺。 -/
lemma dgStrictMappedRoofRefinementEdge_target (P : Set D) (x : D) (y : E)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : F.onClosed.obj t.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappedRoofCorrespondenceTarget A D E F P x y).app (Opposite.op ⦋1⦌)
      (dgStrictMappedRoofRefinementEdge A D E F P x y r f).edge =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A E y).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ (Over.homMk (F.onClosed.map r.hom.left) rfl :
        Over.mk (F.onClosed.map r.hom.left ≫ f) ⟶
        Over.mk f)) := by
  have h := congrArg (fun G => G.app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofRefine A D E F P x y r f)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofNerveMap_target A D E F P x y)
  refine h.trans ?_
  exact congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A E y).app (Opposite.op ⦋1⦌) z)
    (nerveMap_app_mk₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofNumerator A D E F P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofRefine A D E F P x y r f))

/-- 実細分辺の元の始域成分は、指定閉細分射の実閉辺そのもの。 -/
lemma dgStrictMappedRoofRefinementEdge_source (P : Set D) (x : D) (y : E)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : F.onClosed.obj t.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌)
      ((pullback.snd _ _ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappedRoofCorrespondence A D E F P x y ⟶ _).app (Opposite.op ⦋1⦌)
        (dgStrictMappedRoofRefinementEdge A D E F P x y r f).edge) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.hom.left).edge := by
  rw [dgStrictMappedRoofRefinementEdge_projection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_edge_source]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
