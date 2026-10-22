module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramComma
public import SerrePositivity.InfinityCategories.F2.Ind.CommaPostcomp
public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanCommaIso

/-!
概要：元の全図式 comma を各頂点の同じ実 Ind comma へ評価する。
方針：全図式 Yoneda の厳密な可換性と、終点を正規化した comma の後合成を使う。
規約：元の始点図式と元の全錐の射を保持。使われ方：有限半順序図式表示の貼り合わせと各点 cofinal 性。
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

/-- 元の評価した関手頂点は同じ指定図式の同じ頂点の値。 -/
lemma diagramCommaEvaluation_vertex :
    (evaluateFunctorAt (Y := IndInfinity κ C) (ULift.up k)).app (Opposite.op ⦋0⦌)
      (functorVertex D) = D.app (Opposite.op ⦋0⦌) (ULift.up k) :=
  evaluateFunctorAt_functorVertex _ _

/-- 終点の表示変更を行う前の同じ全 comma 評価。 -/
def diagramCommaEvaluationRaw :=
  commaPostcomp (diagramYoneda κ K C) (indYoneda κ C)
    ((SSet.uliftFunctor.{u + 1, u}).map (evaluateFunctorAt (Y := C) k))
    (evaluateFunctorAt (Y := IndInfinity κ C) (ULift.up k))
    (diagramYoneda_evaluate κ k) (functorVertex D)

/-- 指定元図式の指定値の実 Ind comma への同じ全評価。 -/
def diagramCommaEvaluation : diagramComma κ D ⟶
    leftKanShape (indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k)) :=
  diagramCommaEvaluationRaw κ D k ≫ eqToHom
    (congrArg (leftKanShape (indYoneda κ C)) (diagramCommaEvaluation_vertex κ D k))

/-- 元の C の全図式への射影の評価を厳密に回収する。 -/
lemma diagramCommaEvaluation_projection : diagramCommaEvaluation κ D k ≫
    leftKanProjection (indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k)) =
      diagramCommaProjection κ D ≫
        (SSet.uliftFunctor.{u + 1, u}).map (evaluateFunctorAt (Y := C) k) := by
  rw [diagramCommaEvaluation, Category.assoc, leftKanShapeTransport_projection
    (indYoneda κ C) (diagramCommaEvaluation_vertex κ D k)]
  exact commaPostcomp_projection _ _ _ _ _ _

/-- 任意のパラメータの全変換は、同じ元の全変換の頂点評価そのもの。 -/
lemma diagramCommaEvaluation_uncurry {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D) :
    sliceOverUncurry (q ≫ diagramCommaEvaluation κ D k ≫
      pullback.snd (indYoneda κ C) (sliceOverProjection (SSet.yonedaEquiv.symm
        (D.app (Opposite.op ⦋0⦌) (ULift.up k))))) =
    sliceOverUncurry (q ≫ pullback.snd (diagramYoneda κ K C)
      (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex D)))) ≫
        evaluateFunctorAt (Y := IndInfinity κ C) (ULift.up k) := by
  have h := commaTransport_uncurry (indYoneda κ C) (diagramCommaEvaluation_vertex κ D k)
    (q ≫ diagramCommaEvaluationRaw κ D k)
  have he := commaPostcomp_uncurry (diagramYoneda κ K C) (indYoneda κ C)
    ((SSet.uliftFunctor.{u + 1, u}).map (evaluateFunctorAt (Y := C) k))
    (evaluateFunctorAt (Y := IndInfinity κ C) (ULift.up k))
    (diagramYoneda_evaluate κ k) (functorVertex D) q
  simpa only [diagramCommaEvaluation, Category.assoc] using h.trans he

/-- 同じ標準余錐の評価は、元の scalar comma の標準余錐の制限そのもの。 -/
lemma diagramCommaEvaluation_coconeMap :
    joinMap (diagramCommaEvaluation κ D k) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (leftKanCanonicalCocone (indYoneda κ C) (𝟙 (IndInfinity κ C))
        (D.app (Opposite.op ⦋0⦌) (ULift.up k))).val =
    (diagramCommaCocone κ D).val ≫
      evaluateFunctorAt (Y := IndInfinity κ C) (ULift.up k) := by
  change joinMap _ (𝟙 Δ[0]) ≫ (sliceOverUncurry _ ≫ 𝟙 _) = _
  rw [Category.comp_id, ← sliceOverUncurry_precomp]
  simpa only [Category.id_comp, diagramCommaCocone] using
    diagramCommaEvaluation_uncurry κ D k (𝟙 _)

end SerrePositivity.InfinityCategories.F2.Ind
