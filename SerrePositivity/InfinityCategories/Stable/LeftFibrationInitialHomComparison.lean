module
public import SerrePositivity.InfinityCategories.Stable.LeftFibrationInitialPiZero

/-! # 始対象を持つ left fibration の実際の表現可能な比較

概要：fiber から底の左写像空間への比較射は単体的ホモトピー同値となる。
方針：始対象性で自明になる終点評価の切断を選び、もう一方の射影と左模型の同型へ合成する。
規約：切断の選択を含む。使われ方：余錐空間とループ模型の写像空間での比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始対象性による終点評価の自明 fibration の切断を一つ選ぶ。
方針：既存の切断の存在定理を使う。
規約：底や終点に関する自然性はこの定義だけでは主張しない。使われ方：実際の比較射。 -/
def leftFibrationInitialSection {E B : SSet.{u}} (p : E ⟶ B) (c : E _⦋0⦌)
    (hc : IsInitialVertex c) (y : B _⦋0⦌) : vertexFiber p y ⟶ leftFibrationInitialTotal p c y := by
  have := leftFibrationInitialEvaluation_trivialKanFibration p c hc y
  exact Classical.choose (trivialKanFibration_exists_section (leftFibrationInitialEvaluation p c y))

/-- 概要：選んだ切断を終点評価で戻すと恒等射になる。
方針：切断の選択の仕様を読む。
規約：厳密な等号。使われ方：比較射の π₀ の計算。 -/
lemma leftFibrationInitialSection_evaluation {E B : SSet.{u}} (p : E ⟶ B) (c : E _⦋0⦌)
    (hc : IsInitialVertex c) (y : B _⦋0⦌) :
    leftFibrationInitialSection p c hc y ≫ leftFibrationInitialEvaluation p c y = 𝟙 _ := by
  have := leftFibrationInitialEvaluation_trivialKanFibration p c hc y
  exact Classical.choose_spec
    (trivialKanFibration_exists_section (leftFibrationInitialEvaluation p c y))

/-- 概要：始対象を持つ left fibration の fiber から底の左写像空間への比較射。
方針：終点評価の切断、底への射影、左 pinched 模型の同型を合成する。
規約：順方向は fiber から写像空間。使われ方：余極限の表現可能性の空間による表示。 -/
def leftFibrationInitialHomComparison {E B : SSet.{u}} (p : E ⟶ B) (c : E _⦋0⦌)
    (hc : IsInitialVertex c) (y : B _⦋0⦌) : vertexFiber p y ⟶
      pinchedHomLeft (p.app (Opposite.op ⦋0⦌) c) y :=
  leftFibrationInitialSection p c hc y ≫ leftFibrationInitialProjection p c y ≫
    (leftFibrationInitialBaseIso p c y).hom

/-- 概要：始対象を持つ left fibration の実際の比較射は単体的ホモトピー同値。
方針：自明 fibration の切断の同値性を打ち消しで示し、二つの同値へ合成する。
規約：底の quasicategory 性のみを追加。使われ方：写像空間と fiber の比較。 -/
lemma leftFibrationInitialHomComparison_homotopyEquivalence {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (leftFibrationInitialHomComparison p c hc y) := by
  have : KanComplex (vertexFiber p y) := vertexFiber_kanComplex_of_leftFibration p y
  have : KanComplex (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ p)) y) :=
    vertexFiber_kanComplex_of_leftFibration _ _
  have := leftFibrationInitialEvaluation_trivialKanFibration p c hc y
  have he := isQCatEquivalence_of_trivialKanFibration (leftFibrationInitialEvaluation p c y)
  have hs : IsQCatEquivalence (leftFibrationInitialSection p c hc y) := by
    apply he.cancel_right
    rw [leftFibrationInitialSection_evaluation]
    exact (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  have hq := hs.comp ((isQCatEquivalence_of_trivialKanFibration
    (leftFibrationInitialProjection p c y)).comp
      (qCatEquivalenceOfIso (leftFibrationInitialBaseIso p c y)).isQCatEquivalence)
  exact hq.isSimplicialHomotopyEquivalence

/-- 概要：実際の比較射の π₀ への作用は構成済みの fiber と Hom の同値を与える。
方針：切断で中間空間へ移し、二射影による π₀ の計算則を使う。
規約：Hom への最後の変換は左 pinched 模型の既存の同値。使われ方：二つの比較の一致。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_eq_comparison {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌)
    (a : SSet.π₀ (vertexFiber p y)) :
    leftFibrationInitialFiberPiZeroEquiv p c hc y a =
      pinchedHomLeftPiZeroEquiv (p.app (Opposite.op ⦋0⦌) c) y
        (SSet.mapπ₀ (leftFibrationInitialHomComparison p c hc y) a) := by
  have h := leftFibrationInitialFiberPiZeroEquiv_evaluation p c hc y
    (SSet.mapπ₀ (leftFibrationInitialSection p c hc y) a)
  rw [← SSet.mapπ₀_comp_apply, leftFibrationInitialSection_evaluation, SSet.mapπ₀_id_apply] at h
  simpa only [leftFibrationInitialHomComparison, SSet.mapπ₀_comp_apply] using h

end SerrePositivity.InfinityCategories
