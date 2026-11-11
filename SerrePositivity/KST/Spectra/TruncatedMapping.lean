module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FibrationTower

/-!
概要：点つき写像空間の制限を引き戻して得る切断写像空間の塔。
方針：各段に一つの写像と境界整合条件を加える。
規約：境界比較の射を明示的な単体集合の射として受け取る。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの構造写像を代入するための構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.TruncatedMapping

noncomputable section

variable (X Y A : ℕ → PointedSimplicialSet.{u})
  (i : ∀ n, A n ⟶ X (n + 1))
  (step : ∀ n, (PointedObject.basedHom (X n) (Y n)).right ⟶
    (PointedObject.basedHom (A n) (Y (n + 1))).right)

/-- 概要：切断写像空間とその最終段への評価を同時に構成する。
方針：次段の写像の制限と前段からの境界比較を引き戻す。
規約：構造写像の作用に相当する step は実際の単体集合の射。
使われ方：BF 1978 §2。n 段までのスペクトルの写像空間。 -/
def stage : (n : ℕ) → Σ T : SSet.{u}, T ⟶ (PointedObject.basedHom (X n) (Y n)).right
  | 0 => ⟨(PointedObject.basedHom (X 0) (Y 0)).right, 𝟙 _⟩
  | n + 1 =>
    let prev := stage n
    ⟨pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i n) (Y (n + 1))) (prev.2 ≫ step n), pullback.fst _ _⟩

/-- 概要：切断写像空間の基礎単体集合。
方針：stage の第一成分を取る。
規約：添字 n は零段から n 段まで。
使われ方：HTT A.3.3。逆向きの塔の対象。 -/
abbrev space (n : ℕ) : SSet.{u} := (stage X Y A i step n).1

/-- 概要：切断写像から最後の段の写像を取り出す。
方針：stage の第二成分を取る。
規約：行き先は通常の点つき写像空間。
使われ方：BF 1978 §2。次段の整合条件。 -/
abbrev evaluation (n : ℕ) : space X Y A i step n ⟶
    (PointedObject.basedHom (X n) (Y n)).right := (stage X Y A i step n).2

/-- 概要：最後の一段を忘れる写像。
方針：切断写像空間を定義した引き戻しの第二射影。
規約：n + 1 段から n 段へ。
使われ方：BF 1978 §2。Hom の塔の遷移。 -/
def restriction (n : ℕ) : space X Y A i step (n + 1) ⟶ space X Y A i step n :=
  pullback.snd _ _

/-- 概要：切断写像の最終段は前段との境界整合条件を満たす。
方針：引き戻しの可換条件を使う。
規約：単体集合の射の厳密な等式。
使われ方：BF 1978 §2。スペクトルの射の可換条件との照合。 -/
@[reassoc]
theorem evaluation_condition (n : ℕ) :
    evaluation X Y A i step (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i n) (Y (n + 1)) =
      restriction X Y A i step n ≫ evaluation X Y A i step n ≫ step n :=
  pullback.condition

/-- 概要：構造の単射性と標的の Kan 性から切断の遷移は fibration。
方針：点つき Hom の制限の fibration を引き戻す。
規約：step に余分なホモトピー論的条件は不要。
使われ方：BF 1978 §2、HTT A.3.3。Hom の局所 Kan 性の中核。 -/
theorem restriction_fibration (n : ℕ) [Mono (i n).right]
    [KanComplex (Y (n + 1)).right] : Fibration (restriction X Y A i step n) := by
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i n) (Y (n + 1))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration (i n) (Y (n + 1))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_pullback_snd _ _

/-- 概要：全切断に整合する写像の単体集合。
方針：切断写像空間の塔の極限を取る。
規約：実際のスペクトルへの適用には step の構成と可換条件の照合が必要。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの Hom を与える極限。 -/
abbrev total : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (space X Y A i step) (restriction X Y A i step)

/-- 概要：初段への写像空間の射影は Kan fibration。
方針：単射に沿う点つき Hom の制限と塔の相対充填を組み合わせる。
規約：Ω 条件は不要。
使われ方：BF 1978 §2、HTT A.3.3。局所 Kan 性の証明。 -/
theorem total_projection_fibration [∀ n, Mono (i n).right] [∀ n, KanComplex (Y n).right] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (space X Y A i step)
      (restriction X Y A i step) 0) := by
  let : ∀ n, Fibration (restriction X Y A i step n) := fun n ↦
    restriction_fibration X Y A i step n
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_zero_fibration _ _

/-- 概要：整合写像の指定段での評価。
方針：切断への射影とその最終段の評価を合成する。
規約：単体集合の全次数での評価。
使われ方：BF 1978 §2。整合写像と段ごとの可換条件との比較。 -/
def totalEvaluation (n : ℕ) : total X Y A i step ⟶
    (PointedObject.basedHom (X n) (Y n)).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ n ≫ evaluation X Y A i step n

/-- 概要：整合写像の各段への評価は境界条件を満たす。
方針：引き戻しの可換条件と塔の整合条件を合成する。
規約：ホモトピーを介さない厳密な等式。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの射との照合。 -/
@[reassoc]
theorem totalEvaluation_condition (n : ℕ) :
    totalEvaluation X Y A i step (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i n) (Y (n + 1)) =
      totalEvaluation X Y A i step n ≫ step n := by
  dsimp only [totalEvaluation]
  rw [Category.assoc, evaluation_condition, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp]
  rfl

/-- 概要：単射構造を持つ源と段ごとに Kan な標的の整合写像空間は Kan。
方針：初段の点つき Hom の Kan 性と fibration の塔の補題を使う。
規約：この段階では step を具体的なスペクトルから構成したとは主張しない。
使われ方：BF 1978 §2、HTT A.3.3。局所 Kan 性の構成部品。 -/
instance total_kanComplex [∀ n, Mono (i n).right] [∀ n, KanComplex (Y n).right] :
    KanComplex (total X Y A i step) := by
  let : ∀ n, Fibration (restriction X Y A i step n) := fun n ↦
    restriction_fibration X Y A i step n
  let : KanComplex (space X Y A i step 0) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit_kanComplex _ _

end

end SerrePositivity.KST.Spectra.TruncatedMapping
