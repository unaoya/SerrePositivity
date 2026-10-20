module

public import SerrePositivity.InfinityCategories.F1.LeftFibrationInitialEvaluation
public import SerrePositivity.InfinityCategories.F1.PullbackNerveFiber

/-!
概要：指定 fiber の全ての点を同時に、coslice 全体上の底を保つ族へ延長する。
方針：恒等錐での評価の自明 Kan 性から切断を選び、元の相対関手空間で展開する。
規約：全対象にまたがる一つの射を構成し、恒等錐での始点を全次数で厳密に保つ。
使われ方：恒等射の点から、Hom 関手の unstraightening への大域的な比較を作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 恒等錐での相対評価を、指定した底の頂点の fiber へ厳密に正規化する。 -/
def leftFibrationCoslicePointEvaluate {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    relativeFunctorSpace p (sliceUnderProjection (SSet.yonedaEquiv.symm b)) ⟶ vertexFiber p b :=
  relativeFunctorEvaluate p (sliceUnderProjection (SSet.yonedaEquiv.symm b))
    (cosliceIdentityCone b) ≫
    eqToHom (congrArg (vertexFiber p) (cosliceIdentityCone_projection b))

/-- 指定 fiber への正規化済みの評価は、自明 Kan fibration。 -/
lemma leftFibrationCoslicePointEvaluate_trivialKanFibration
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    TrivialKanFibration (leftFibrationCoslicePointEvaluate p b) := by
  have h := leftFibration_cosliceIdentityEvaluation_trivialKanFibration p b
  exact ⟨trivialKanFibrations.comp_mem _ _ h.mem (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 指定 fiber 全体をパラメーターとして、coslice 全体上の相対関手を同時に選ぶ。 -/
def leftFibrationCoslicePointSection {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    vertexFiber p b ⟶ relativeFunctorSpace p (sliceUnderProjection (SSet.yonedaEquiv.symm b)) := by
  have := leftFibrationCoslicePointEvaluate_trivialKanFibration p b
  exact (trivialKanFibration_exists_section (leftFibrationCoslicePointEvaluate p b)).choose

/-- 同じ切断は、恒等錐で評価すると全 fiber 上の恒等射を厳密に回収する。 -/
lemma leftFibrationCoslicePointSection_evaluate {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    leftFibrationCoslicePointSection p b ≫ leftFibrationCoslicePointEvaluate p b = 𝟙 _ := by
  have := leftFibrationCoslicePointEvaluate_trivialKanFibration p b
  exact (trivialKanFibration_exists_section (leftFibrationCoslicePointEvaluate p b)).choose_spec

/-- 指定 fiber の全ての点から coslice の全対象へ向かう、一つの底上の族。 -/
def leftFibrationCoslicePointFamily {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm b) ⊗ vertexFiber p b ⟶ E :=
  relativeFunctorUncurry (leftFibrationCoslicePointSection p b)

/-- 全体の族は、coslice の元の射影を厳密に被覆する。 -/
lemma leftFibrationCoslicePointFamily_projection {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    leftFibrationCoslicePointFamily p b ≫ p =
      fst _ _ ≫ sliceUnderProjection (SSet.yonedaEquiv.symm b) :=
  relativeFunctorUncurry_projection (leftFibrationCoslicePointSection p b)

/-- 恒等錐への制限は、指定した全ての fiber 点の包含と厳密に一致する。 -/
lemma leftFibrationCoslicePointFamily_identity {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    lift (SSet.const (cosliceIdentityCone b)) (𝟙 (vertexFiber p b)) ≫
      leftFibrationCoslicePointFamily p b = vertexFiberι p b := by
  calc
    _ = leftFibrationCoslicePointSection p b ≫
        relativeFunctorEvaluate p (sliceUnderProjection (SSet.yonedaEquiv.symm b))
          (cosliceIdentityCone b) ≫ vertexFiberι p
            ((sliceUnderProjection (SSet.yonedaEquiv.symm b)).app _ (cosliceIdentityCone b)) := rfl
    _ = leftFibrationCoslicePointSection p b ≫ leftFibrationCoslicePointEvaluate p b ≫
        vertexFiberι p b := by
      dsimp only [leftFibrationCoslicePointEvaluate]
      rw [Category.assoc, vertexFiberTransport_ι p (cosliceIdentityCone_projection b)]
    _ = vertexFiberι p b := by
      rw [← Category.assoc, leftFibrationCoslicePointSection_evaluate, Category.id_comp]

end SerrePositivity.InfinityCategories
