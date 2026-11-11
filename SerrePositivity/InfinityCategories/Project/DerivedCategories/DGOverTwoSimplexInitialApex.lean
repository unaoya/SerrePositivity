module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOverTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOverVertexInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTetrahedronInitialDiagonal

/-! # 実 over 二単体の閉始点細分の新 apex の合成分母表示

概要：任意の実 over 二単体の細分後の始頂点の構造辺を、同じ閉射の実合成で表す。
方針：回収四面体の対角辺公式を使い、元の始頂点の分母条件と合成閉性を接続する。
規約：元の P を保つ。使われ方：同じ細分辺錐の実分母 over への持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (x : D)
variable (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋2⦌) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
  (((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)).obj 0))


/-- 元の over 二単体の始点対角実辺から回収する閉射。 -/
def dgOverTwoSimplexInitialClosed :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)))).edgeClosed 0 1 (by decide)

/-- 回収した元の対角閉射の実辺は、元の始頂点の構造辺。 -/
lemma dgOverTwoSimplexInitialClosed_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (dgOverTwoSimplexInitialClosed A D x σ)).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 σ))).edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexEdge_closed_normal A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ))))).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_initialDiagonal _ σ)

/-- 細分後の始頂点の構造辺は、同じ追加閉射と元の対角閉射の合成。 -/
lemma dgOverTwoSimplexInitialRefinement_apex_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement A D x σ q s)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (s ≫ dgOverTwoSimplexInitialClosed A D x σ)).edge := by
  have hr := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement_tetrahedron A D x σ q s)
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement A D x σ q s)) =
      SSet.yonedaEquiv ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)) q s))
    at hr
  rw [Equiv.apply_symm_apply] at hr
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_initialDiagonal _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement A D x σ q s)).symm.trans
      ((congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t)) hr).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronInitialRefinement_initialDiagonal A D
          (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)) q s))

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 元の始頂点と追加閉射が実分母なら、同じ細分後の始頂点も実分母。 -/
lemma dgOverTwoSimplexInitialRefinement_apex_mem (P : Set D)
    (hA : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 σ)))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement A D x σ q s))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex at hA ⊢
  rw [dgOverTwoSimplexInitialRefinement_apex_edge]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P s (dgOverTwoSimplexInitialClosed A D x σ) hs
  rw [dgOverTwoSimplexInitialClosed_edge]
  exact hA

end SerrePositivity.InfinityCategories.Project.DerivedCategories
