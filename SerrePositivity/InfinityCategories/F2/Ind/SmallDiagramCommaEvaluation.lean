module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.SmallDiagramComma

/-!
概要：小さい表示添字の各頂点評価と元の標準全余錐を照合する。
方針：元の実比較同型を全評価へ合成し、射影と全余錐の等式を保つ。
規約：cofinal 性は未主張。使われ方：有限半順序図式の各点密度への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) (k : K _⦋0⦌)

/-- 同じ小さい添字の持ち上げから、元の指定値の実 comma への評価。 -/
def smallDiagramCommaEvaluation : (SSet.uliftFunctor.{u + 1, u}).obj
    (smallDiagramComma κ D) ⟶
      leftKanShape (indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k)) :=
  (smallDiagramCommaIso κ D).hom ≫ diagramCommaEvaluation κ D k

/-- 元の C の図式の同じ頂点での評価を厳密に回収する。 -/
lemma smallDiagramCommaEvaluation_projection : smallDiagramCommaEvaluation κ D k ≫
    leftKanProjection (indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k)) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (smallDiagramCommaProjection κ D ≫ evaluateFunctorAt (Y := C) k) := by
  rw [smallDiagramCommaEvaluation, Category.assoc, diagramCommaEvaluation_projection,
    ← Category.assoc, smallDiagramCommaIso_projection, ← Functor.map_comp]

/-- 小さい標準全余錐の評価は、元の scalar 標準全余錐の同じ評価による制限。 -/
lemma smallDiagramCommaEvaluation_coconeMap :
    joinMap (smallDiagramCommaEvaluation κ D k) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (leftKanCanonicalCocone (indYoneda κ C) (𝟙 (IndInfinity κ C))
        (D.app (Opposite.op ⦋0⦌) (ULift.up k))).val =
    (smallDiagramCommaCocone κ D).val ≫
      evaluateFunctorAt (Y := IndInfinity κ C) (ULift.up k) := by
  have hj := joinMap_comp (smallDiagramCommaIso κ D).hom (diagramCommaEvaluation κ D k)
    (𝟙 (Δ[0] : SSet.{u + 1})) (𝟙 (Δ[0] : SSet.{u + 1}))
  simp only [Category.id_comp] at hj
  rw [smallDiagramCommaEvaluation, hj, Category.assoc,
    diagramCommaEvaluation_coconeMap, ← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
