module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOverTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementPositiveFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementCongruence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementTriangle

/-! # 実 over 二単体の閉始点細分の二つの脚面

概要：細分後の正番号二面の回収三角形は、元の脚面の同じ閉始点細分。
方針：四面体の面公式と一般細分の正番号面との可換性、元の対象等式を接続する。
規約：追加閉実辺を保持。使われ方：辺錐の二脚と固定頂点脚の一致。
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


/-- 元の正番号面の回収三角形は、元の回収四面体の対応する正番号面。 -/
lemma dgOverTwoSimplexPositiveFace_triangle (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ i.succ.castSucc (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ i.succ σ)) := by
  have h := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face _ σ i.succ)
  rw [stdSimplex.yonedaEquiv_δ_comp] at h
  exact h

/-- 元の各正番号面の回収三角形の始対象は、同じ回収四面体の始対象。 -/
lemma dgOverTwoSimplexPositiveFace_source (i : Fin 2) :
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)).obj 0 =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ i.succ σ))).obj 0 := by
  fin_cases i
  · exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 => t.obj 0)
      (dgOverTwoSimplexPositiveFace_triangle A D x σ 0)
  · exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 => t.obj 0)
      (dgOverTwoSimplexPositiveFace_triangle A D x σ 1)

/-- 細分後の各脚面は、元の同じ脚三角形の同じ閉始点細分として回収される。 -/
lemma dgOverTwoSimplexInitialRefinement_face_positive (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ i.succ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement A D x σ q s)) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D
          (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ i.succ σ))) q
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (dgOverTwoSimplexPositiveFace_source A D x σ i))) := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron_face _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 0 σ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialTetrahedron A D x σ q s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialTetrahedron_face0 A D x σ q s) i.succ
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr
    (dgOverTwoSimplexPositiveFace_triangle A D x σ i) q q s
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (dgOverTwoSimplexPositiveFace_source A D x σ i))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s _).symm
  fin_cases i
  · have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_face_positive A D
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)) q s (1 : Fin 4) (by decide)
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at hp
    have hh : SSet.stdSimplex.δ (1 : Fin 4) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialTetrahedron A D x σ q s =
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D
            (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 σ))) q
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (dgOverTwoSimplexPositiveFace_source A D x σ 0))) := by
      unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialTetrahedron
      rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (hp.trans hc)
    exact hf.trans hh
  · have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_face_positive A D
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)) q s (2 : Fin 4) (by decide)
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at hp
    have hh : SSet.stdSimplex.δ (2 : Fin 4) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialTetrahedron A D x σ q s =
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D
            (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 2 σ))) q
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (dgOverTwoSimplexPositiveFace_source A D x σ 1))) := by
      unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialTetrahedron
      rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (hp.trans hc)
    exact hf.trans hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
