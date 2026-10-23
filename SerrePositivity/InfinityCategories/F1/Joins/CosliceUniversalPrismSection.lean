module

public import SerrePositivity.InfinityCategories.F1.Joins.CosliceUniversalPrismLift
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationCoslicePointUniqueness
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：標準 coslice 区間の持ち上げの終点を、大域的な相対関手空間へ移す。
方針：終点を curry し、恒等錐での値を正規化済みの評価で計算する。
規約：任意のパラメーターを保ち、同じ始点を持つ標準切断との一意性を使う。
使われ方：恒等点からの大域比較を、同じ区間族の輸送の終点と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 恒等錐での正規化した評価を全空間へ含めると、元の関手の頂点評価となる。 -/
lemma leftFibrationCoslicePointEvaluate_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    leftFibrationCoslicePointEvaluate p b ≫ vertexFiberι p b =
      vertexFiberι ((ihom (sliceUnder (SSet.yonedaEquiv.symm b))).map p)
        (functorVertex (sliceUnderProjection (SSet.yonedaEquiv.symm b))) ≫
        evaluateFunctorAt (cosliceIdentityCone b) := by
  dsimp only [leftFibrationCoslicePointEvaluate]
  rw [Category.assoc, vertexFiberTransport_ι p (cosliceIdentityCone_projection b)]
  exact relativeFunctorEvaluate_ι p _ (cosliceIdentityCone b)

/-- 標準区間族の持ち上げの終点を、任意のパラメーターの相対関手として表す。 -/
def cosliceUniversalPrismLiftSectionFamily {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) (P : SSet.{u}) :
    P ⟶ relativeFunctorSpace p (sliceUnderProjection (SSet.yonedaEquiv.symm b)) :=
  relativeFunctorCurry
    (fst (sliceUnder (SSet.yonedaEquiv.symm b)) P ≫ cosliceUniversalPrismLiftEndpoint p b d hd)
    (by rw [Category.assoc, cosliceUniversalPrismLiftEndpoint_projection])

/-- 終点の族は、正規化した恒等錐での評価で同じ指定始点を厳密に回収する。 -/
lemma cosliceUniversalPrismLiftSectionFamily_evaluate {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) (P : SSet.{u}) :
    cosliceUniversalPrismLiftSectionFamily p b d hd P ≫
      leftFibrationCoslicePointEvaluate p b =
        SSet.const (⟨d, by rw [PinchedHom.constant_zero]; exact hd⟩ :
          (vertexFiber p b) _⦋0⦌) := by
  apply (cancel_mono (vertexFiberι p b)).1
  rw [Category.assoc, leftFibrationCoslicePointEvaluate_ι]
  change curry (fst _ P ≫ cosliceUniversalPrismLiftEndpoint p b d hd) ≫
    evaluateFunctorAt (cosliceIdentityCone b) = _
  rw [curry_evaluateFunctorAt_vertex, ← Category.assoc, lift_fst, SSet.const_comp,
    cosliceUniversalPrismLiftEndpoint_identity]
  rfl

/-- 同じ持ち上げの終点は、全対象の相対関手空間で標準の始点延長と同型。 -/
def cosliceUniversalPrismLiftSectionFamily_comparisonIso
    {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) (P : SSet.{u}) :
    FunctorIso (cosliceUniversalPrismLiftSectionFamily p b d hd P)
      (SSet.const (⟨d, by rw [PinchedHom.constant_zero]; exact hd⟩ :
        (vertexFiber p b) _⦋0⦌) ≫ leftFibrationCoslicePointSection p b) := by
  apply leftFibrationCoslicePointEvaluate_equalIso p b
  rw [cosliceUniversalPrismLiftSectionFamily_evaluate, Category.assoc,
    leftFibrationCoslicePointSection_evaluate, Category.comp_id]

end SerrePositivity.InfinityCategories
