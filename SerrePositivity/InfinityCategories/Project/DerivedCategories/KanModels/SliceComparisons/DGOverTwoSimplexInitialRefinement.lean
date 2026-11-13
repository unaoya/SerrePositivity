module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInitialRefinementAvoidingFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofSliceTetrahedronFaces

/-! # 点上の実 over 二単体の閉始点細分

概要：回収四面体の始点だけを閉射で細分し、元の零面を保つ同じ over 二単体へ戻す。
方針：一般細分の零面保存と、指定終点の join による逆回収を接続する。
規約：実分母性は別に照合する。使われ方：高次充填の指定辺錐の共通化。
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

/-- 実 over 二単体の回収四面体を、同じ閉射で始点細分した実四面体。 -/
def dgOverTwoSimplexInitialTetrahedron : Δ[3] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)) q s)

/-- 細分四面体の零面は、元の over 二単体の零面の回収三角形のまま。 -/
lemma dgOverTwoSimplexInitialTetrahedron_face0 :
    SSet.stdSimplex.δ (0 : Fin 4) ≫ dgOverTwoSimplexInitialTetrahedron A D x σ q s =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 0 σ) := by
  unfold dgOverTwoSimplexInitialTetrahedron
  rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  have h₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_face_zero A D
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ)) q s
  have he := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face _ σ (0 : Fin 3))
  rw [stdSimplex.yonedaEquiv_δ_comp] at he
  exact (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (h₀.trans he)).trans
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm_apply_apply _)

/-- 元の零面を保つ、同じ閉射による実 over 二単体の始点細分。 -/
def dgOverTwoSimplexInitialRefinement :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 0 σ))
    (dgOverTwoSimplexInitialTetrahedron A D x σ q s)
    (dgOverTwoSimplexInitialTetrahedron_face0 A D x σ q s)

/-- 細分した over 二単体の回収四面体は、入力の同じ閉始点細分四面体。 -/
lemma dgOverTwoSimplexInitialRefinement_tetrahedron :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ (dgOverTwoSimplexInitialRefinement A D x σ q s) =
      dgOverTwoSimplexInitialTetrahedron A D x σ q s := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 0).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 0).hom ≫ dgOverTwoSimplexInitialTetrahedron A D x σ q s) = _
  rw [Iso.inv_hom_id_assoc]

/-- 細分した実 over 二単体は、元の指定零面を厳密に保つ。 -/
lemma dgOverTwoSimplexInitialRefinement_face0 :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 0 (dgOverTwoSimplexInitialRefinement A D x σ q s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 0 σ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron_face _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 0 σ))
    (dgOverTwoSimplexInitialTetrahedron A D x σ q s)
    (dgOverTwoSimplexInitialTetrahedron_face0 A D x σ q s) 0).trans
      (dgOverTwoSimplexInitialTetrahedron_face0 A D x σ q s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
