module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGVerdierDiagramTriangleHorn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofSliceFourSimplexInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.FullSubcomplexThreeSimplexLift

/-! # 実四次充填から図式二単体と三辺錐の整合性を回収する

概要：指定四次ホーンの実充填を、実分母部分圏の三単体へ戻して全指定四面を保存する。
方針：終点固定の over 三単体を回収し、二つの指定面の所属から全部分複体へ上げる。
規約：四次充填の存在は入力。使われ方：高次残差方程式の解と実有限図式の接続。
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
  (C.leg (K.δ 0 (K.δ i σ)))) (F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 指定四次ホーンの実充填から回収する、終点を固定した実 over 三単体。 -/
def dgVerdierDiagramTriangleOverFiller
    (hF : (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋3⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHornOverFiller _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleBoundary A D C σ H) F hF

/-- 回収した実 over 三単体の零面は、元の指定実図式二単体。 -/
lemma dgVerdierDiagramTriangleOverFiller_face0
    (hF : (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 0 (dgVerdierDiagramTriangleOverFiller A D C σ H F hF) = (f.app _ σ).val :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHornOverFiller_face _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleBoundary A D C σ H) F hF 0

/-- 回収した実 over 三単体の残る三面は、元の三つの指定実辺錐。 -/
lemma dgVerdierDiagramTriangleOverFiller_face_cone
    (hF : (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) (i : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ i.succ (dgVerdierDiagramTriangleOverFiller A D C σ H F hF) =
      (H i).simplex.val := by
  fin_cases i
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHornOverFiller_face _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleBoundary A D C σ H) F hF 1
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHornOverFiller_face _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleBoundary A D C σ H) F hF 2
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHornOverFiller_face _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleBoundary A D C σ H) F hF 3

/-- 同じ実充填三単体を、元の実分母部分圏へ持ち上げる。 -/
def dgVerdierDiagramTriangleFiller
    (hF : (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋3⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullSubcomplexThreeSimplexLift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x)
    (dgVerdierDiagramTriangleOverFiller A D C σ H F hF) (f.app _ σ) (H 0).simplex
    (dgVerdierDiagramTriangleOverFiller_face0 A D C σ H F hF)
    (dgVerdierDiagramTriangleOverFiller_face_cone A D C σ H F hF 0)

/-- 実分母部分圏の充填の零面は、元の指定図式二単体。 -/
lemma dgVerdierDiagramTriangleFiller_face0
    (hF : (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (dgVerdierDiagramTriangleFiller A D C σ H F hF) =
      f.app _ σ :=
  Subtype.ext (dgVerdierDiagramTriangleOverFiller_face0 A D C σ H F hF)

/-- 実分母部分圏の充填は、元の三つの指定実辺錐を全て厳密に保つ。 -/
lemma dgVerdierDiagramTriangleFiller_face_cone
    (hF : (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) (i : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ (dgVerdierDiagramTriangleFiller A D C σ H F hF) =
      (H i).simplex :=
  Subtype.ext (dgVerdierDiagramTriangleOverFiller_face_cone A D C σ H F hF i)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
