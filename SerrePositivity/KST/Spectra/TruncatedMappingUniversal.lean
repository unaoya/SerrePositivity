module

public import SerrePositivity.KST.Spectra.TruncatedMapping

/-!
概要：切断写像空間の極限の、各段評価による普遍性。
方針：整合する写像の族を段ごとの引き戻しへ帰納的に持ち上げる。
規約：任意の単体集合をパラメータとする。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの射・単体的合成の構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.TruncatedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y A : ℕ → PointedSimplicialSet.{u}) (i : ∀ n, A n ⟶ X (n + 1))
  (step : ∀ n, (PointedObject.basedHom (X n) (Y n)).right ⟶
    (PointedObject.basedHom (A n) (Y (n + 1))).right)

variable {B : SSet.{u}}
  (f : ∀ n, B ⟶ (PointedObject.basedHom (X n) (Y n)).right)
  (hf : ∀ n, f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i n) (Y (n + 1)) = f n ≫ step n)

/-- 概要：各段の整合する写像を切断写像空間へ持ち上げる。
方針：最終段への評価を記録しながら引き戻しへ帰納的に持ち上げる。
規約：任意の単体集合 B をパラメータに取る。
使われ方：BF 1978 §2、HTT A.3.3。極限への普遍的な射。 -/
def familyStage : ∀ n, {l : B ⟶ space X Y A i step n //
    l ≫ evaluation X Y A i step n = f n}
  | 0 => ⟨f 0, Category.comp_id _⟩
  | n + 1 =>
    let prev := familyStage n
    ⟨pullback.lift (f (n + 1)) prev.val ((hf n).trans
      ((congrArg (fun k ↦ k ≫ step n) prev.property).symm.trans (Category.assoc _ _ _))),
      pullback.lift_fst _ _ _⟩

/-- 概要：切断への普遍的な持ち上げは塔の制限と整合する。
方針：引き戻しの第二射影の計算則を使う。
規約：任意の段 n。
使われ方：HTT A.3.3。切断の持ち上げを逆極限にまとめる。 -/
theorem familyStage_restriction (n : ℕ) :
    (familyStage X Y A i step f hf (n + 1)).val ≫ restriction X Y A i step n =
      (familyStage X Y A i step f hf n).val := by
  exact pullback.lift_snd _ _ _

/-- 概要：各段で整合する写像の族から全切断の極限への射を作る。
方針：切断ごとの引き戻しへの持ち上げを塔の極限へまとめる。
規約：Kan 性は不要。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの写像空間の普遍性。 -/
def familyLift : B ⟶ total X Y A i step :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift _ _ (fun n ↦ (familyStage X Y A i step f hf n).val)
    (familyStage_restriction X Y A i step f hf)

/-- 概要：全切断の極限への持ち上げを評価すると指定の写像に戻る。
方針：塔への持ち上げと各切断の評価の計算を合成する。
規約：任意の段 n。
使われ方：BF 1978 §2。単位・合成の成分ごとの計算。 -/
@[reassoc (attr := simp)]
theorem familyLift_evaluation (n : ℕ) :
    familyLift X Y A i step f hf ≫ totalEvaluation X Y A i step n = f n := by
  dsimp only [familyLift, totalEvaluation]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection]
  exact (familyStage X Y A i step f hf n).property

/-- 概要：切断写像空間への射は全ての下位段への評価で決まる。
方針：引き戻しの二つの射影の外延性で帰納する。
規約：評価の番号 k は切断段 n 以下。
使われ方：HTT A.3.3。極限の成分による一意性。 -/
theorem projection_eq_of_evaluations {g h : B ⟶ total X Y A i step}
    (he : ∀ n, g ≫ totalEvaluation X Y A i step n = h ≫ totalEvaluation X Y A i step n)
    (n : ℕ) :
    g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (space X Y A i step) (restriction X Y A i step) n =
      h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (space X Y A i step) (restriction X Y A i step) n := by
  induction n with
  | zero =>
    have hz := he 0
    change g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ 0 ≫ 𝟙 _ =
      h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ 0 ≫ 𝟙 _ at hz
    simpa only [Category.comp_id] using hz
  | succ n ih =>
    apply pullback.hom_ext
    · exact he (n + 1)
    · change (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ (n + 1)) ≫ restriction X Y A i step n =
        (h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ (n + 1)) ≫ restriction X Y A i step n
      rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp]
      exact ih

/-- 概要：整合写像空間への射は各段への評価で決まる。
方針：切断への射影を評価から復元し、塔の極限の一意性を使う。
規約：任意の始域 B。
使われ方：BF 1978 §2、HTT A.3.3。厳密な単位・結合律の検証。 -/
theorem total_hom_ext {g h : B ⟶ total X Y A i step}
    (he : ∀ n, g ≫ totalEvaluation X Y A i step n = h ≫ totalEvaluation X Y A i step n) :
    g = h := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext
  exact projection_eq_of_evaluations X Y A i step he

end

end SerrePositivity.KST.Spectra.TruncatedMapping
