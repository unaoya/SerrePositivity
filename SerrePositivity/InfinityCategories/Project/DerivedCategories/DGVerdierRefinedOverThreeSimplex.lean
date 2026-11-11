module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornRefinementFiller
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramTriangleFiller

/-! # 実分母図式二単体の閉始点細分後の実四単体と over 三単体

概要：細分ホーンの実四次充填を、元の図式二単体を保つ over 三単体へ戻す。
方針：充填の終端面の厳密一致から、点との join による逆写像で over へ戻す。
規約：細分始頂点の実分母性は別に照合する。使われ方：有限共通始錐の二次整合性。
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
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))

/-- 細分した実図式二単体ホーンの充填は、元の指定実図式二単体の四面体を厳密に保つ。 -/
lemma dgVerdierDiagramTriangleRefinedFiller_face0 (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
    (F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    SSet.stdSimplex.δ (0 : Fin 5) ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι.app _ (f.app _ σ)) := by
  rw [← horn.ι_ι_assoc (4 : Fin 5) 0 (by decide), hF,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_preserves_face0]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn_face0 A D C σ H

/-- 同じ閉細分充填から回収する、終点を元の x に固定した実 over 三単体。 -/
def dgVerdierDiagramRefinedOverThreeSimplex (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
    (F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋3⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceThreeSimplexOfFourSimplex _
    (f.app _ σ).val F
    (dgVerdierDiagramTriangleRefinedFiller_face0 A D C σ H q s F hF)

/-- 回収した実 over 三単体の零面は、元の指定図式二単体と厳密に同じ。 -/
lemma dgVerdierDiagramRefinedOverThreeSimplex_face0 (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
    (F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))).δ 0
      (dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι.app _ (f.app _ σ) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceThreeSimplexOfFourSimplex_face _ _ F
    (dgVerdierDiagramTriangleRefinedFiller_face0 A D C σ H q s F hF) 0).trans
      (dgVerdierDiagramTriangleRefinedFiller_face0 A D C σ H q s F hF)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
