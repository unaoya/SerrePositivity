module
public import SerrePositivity.InfinityCategories.Stable.LeftFibrationInitialNaturality

/-! # 始対象による fiber 表示の連結成分での自然性

概要：始対象を持つ left fibration の fiber の coslice 表示は底を保つ関手に自然。
方針：終点評価の π₀ の全射性で中間空間へ持ち上げ、比較 span の二つの可換な正方形を使う。
規約：自然性は π₀ 上の等号。使われ方：図式制限と表現可能な Hom 比較の両立。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始対象を持つ left fibration の fiber の連結成分を底の coslice fiber で表示する。
方針：比較 span の二つの自明 Kan fibration を反転・合成する。
規約：左 pinched 模型への変換の前の同値。使われ方：表示変更を含む自然性の計算。 -/
def leftFibrationInitialFiberCoslicePiZeroEquiv {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌) :
    SSet.π₀ (vertexFiber p y) ≃
      SSet.π₀ (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ p)) y) := by
  have : KanComplex (vertexFiber p y) := vertexFiber_kanComplex_of_leftFibration p y
  have : KanComplex (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ p)) y) :=
    vertexFiber_kanComplex_of_leftFibration _ _
  have := leftFibrationInitialEvaluation_trivialKanFibration p c hc y
  exact (stablePiZeroEquivOfTrivialKanFibration
    (leftFibrationInitialEvaluation p c y)).symm.trans
      (stablePiZeroEquivOfTrivialKanFibration (leftFibrationInitialProjection p c y))

/-- 概要：coslice による連結成分の表示は中間空間の二射影を同一視する。
方針：終点評価の π₀ の同値とその逆を消す。
規約：始対象性を仮定する。使われ方：自然性の証明での中間空間への移行。 -/
lemma leftFibrationInitialFiberCoslicePiZeroEquiv_evaluation {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌)
    (a : SSet.π₀ (leftFibrationInitialTotal p c y)) :
    leftFibrationInitialFiberCoslicePiZeroEquiv p c hc y
      (SSet.mapπ₀ (leftFibrationInitialEvaluation p c y) a) =
    SSet.mapπ₀ (leftFibrationInitialProjection p c y) a := by
  simp only [leftFibrationInitialFiberCoslicePiZeroEquiv, Equiv.trans_apply,
    stablePiZeroEquivOfTrivialKanFibration, Equiv.ofBijective_symm_apply_apply]
  rfl

/-- 概要：coslice 表示から左模型の Hom に移すと既存の表現可能な同値になる。
方針：三つの連結成分の同値の合成の定義を読む。
規約：始点と余極限の選択は固定。使われ方：coslice での自然性を Hom 比較へ移す。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_eq_coslice {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌)
    (a : SSet.π₀ (vertexFiber p y)) :
    leftFibrationInitialFiberPiZeroEquiv p c hc y a =
      pinchedHomLeftPiZeroEquiv (p.app (Opposite.op ⦋0⦌) c) y
        (SSet.mapπ₀ (leftFibrationInitialBaseIso p c y).hom
          (leftFibrationInitialFiberCoslicePiZeroEquiv p c hc y a)) := rfl

/-- 概要：始対象からの fiber の coslice 表示は同じ底上の関手に自然。
方針：終点評価の π₀ の全射性で持ち上げ、二射影の可換性を使う。
規約：像の始点も始対象と仮定し、底の点図式の表示を等号で元へ戻す。
使われ方：余錐の形状制限および二枝交換との比較。 -/
lemma leftFibrationInitialFiberCoslicePiZeroEquiv_naturality
    {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (q : F ⟶ B) [LeftFibration q] (f : E ⟶ F) (hf : f ≫ q = p)
    (c : E _⦋0⦌) (hc : IsInitialVertex c) (d : F _⦋0⦌) (hd : IsInitialVertex d)
    (hcd : f.app (Opposite.op ⦋0⦌) c = d) (y : B _⦋0⦌)
    (a : SSet.π₀ (vertexFiber p y)) :
    SSet.mapπ₀ (eqToHom (congrArg (fun t => vertexFiber (sliceUnderProjection t) y)
      (leftFibrationInitialBaseDiagram_eq p q f hf c d hcd).symm))
        (leftFibrationInitialFiberCoslicePiZeroEquiv q d hd y
          (SSet.mapπ₀ (vertexFiberMap p q f hf y) a)) =
      leftFibrationInitialFiberCoslicePiZeroEquiv p c hc y a := by
  have : KanComplex (vertexFiber p y) := vertexFiber_kanComplex_of_leftFibration p y
  have := leftFibrationInitialEvaluation_trivialKanFibration p c hc y
  obtain ⟨t, rfl⟩ := (stablePiZeroEquivOfTrivialKanFibration
    (leftFibrationInitialEvaluation p c y)).surjective a
  have h := leftFibrationInitialFiberCoslicePiZeroEquiv_evaluation q d hd y
    (SSet.mapπ₀ (leftFibrationInitialTotalMap p q f hf c d hcd y) t)
  rw [← SSet.mapπ₀_comp_apply, leftFibrationInitialTotalMap_evaluation,
    SSet.mapπ₀_comp_apply] at h
  change SSet.mapπ₀ _ (leftFibrationInitialFiberCoslicePiZeroEquiv q d hd y
    (SSet.mapπ₀ (vertexFiberMap p q f hf y)
      (SSet.mapπ₀ (leftFibrationInitialEvaluation p c y) t))) =
    leftFibrationInitialFiberCoslicePiZeroEquiv p c hc y
      (SSet.mapπ₀ (leftFibrationInitialEvaluation p c y) t)
  rw [h, leftFibrationInitialFiberCoslicePiZeroEquiv_evaluation]
  rw [← SSet.mapπ₀_comp_apply, ← SSet.mapπ₀_comp_apply,
    leftFibrationInitialTotalMap_projection]

end SerrePositivity.InfinityCategories
