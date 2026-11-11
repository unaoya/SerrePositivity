module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.MappingPathNaturality

/-!
概要：点つき逆向きの塔の射の mapping path 因子分解を実際の極限へ束ねる。
方針：可換正方形に対する自然性を隣接遷移へ適用し、既存の極限の射を使う。
規約：各段の source、target、定数 path の射を変更しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、Sp の塔の全次数比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

variable (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)

/-- 概要：各段の mapping path を逆向きの塔にする遷移。
方針：元の塔の隣接する可換正方形に mappingPathMap を適用する。
規約：遷移は次段から前段への向き。
使われ方：mapping path の塔の実際の極限の構成。 -/
def mappingPathTowerStep (n : ℕ) : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath (f (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath (f n) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap (f (n + 1)) (f n) (dX n) (dY n) (hf n).symm

/-- 概要：mapping path の塔の遷移は元の源への射影と可換。
方針：可換正方形に対する源射影の自然性を使う。
規約：点つき射の厳密な等式。
使われ方：極限から元の源の極限への射の整合条件。 -/
lemma mappingPathTower_source_comm (n : ℕ) :
    mappingPathTowerStep X Y dX dY f hf n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction (f n) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction (f (n + 1)) ≫ dX n := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_source ..

/-- 概要：mapping path の塔の遷移は元の標的への終点射と可換。
方針：可換正方形に対する終点射の自然性を使う。
規約：元の標的の塔の遷移を保つ。
使われ方：極限から元の標的の極限への射の整合条件。 -/
lemma mappingPathTower_target_comm (n : ℕ) :
    mappingPathTowerStep X Y dX dY f hf n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection (f n) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection (f (n + 1)) ≫ dY n := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_target ..

/-- 概要：定数 path の各段の比較は元の源の塔の遷移と可換。
方針：定数 path の自然性を隣接正方形で使う。
規約：source から mapping path への向きの塔の射。
使われ方：元の極限から中間の極限への比較射。 -/
lemma mappingPathTower_unit_comm (n : ℕ) :
    dX n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit (f n) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit (f (n + 1)) ≫ mappingPathTowerStep X Y dX dY f hf n :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_unit ..).symm

/-- 概要：mapping path の塔の極限から元の源の塔の極限への射。
方針：各段の源射影を整合族の極限の射に束ねる。
規約：基礎単体集合の実際の極限を使い、Kan 性は要求しない。
使われ方：塔の比較を二つの全ての単射への RLP 射へ因子分解する準備。 -/
def mappingPathTowerLimitSource :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath (f n)).right)
        (fun n ↦ (mappingPathTowerStep X Y dX dY f hf n).right) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (dX n).right) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap (fun n ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction (f n)).right) (by
    intro n
    simpa only [Under.comp_right] using
      congrArg Under.Hom.right (mappingPathTower_source_comm X Y dX dY f hf n))

/-- 概要：mapping path の塔の極限から元の標的の塔の極限への射。
方針：各段の終点射を整合族の極限の射に束ねる。
規約：基礎単体集合の射として定義する。
使われ方：塔の元の比較射の因子分解の右因子。 -/
def mappingPathTowerLimitTarget :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath (f n)).right)
        (fun n ↦ (mappingPathTowerStep X Y dX dY f hf n).right) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (Y n).right) (fun n ↦ (dY n).right) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap (fun n ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection (f n)).right) (by
    intro n
    simpa only [Under.comp_right] using
      congrArg Under.Hom.right (mappingPathTower_target_comm X Y dX dY f hf n))

/-- 概要：元の源の極限から mapping path の塔の極限への定数 path の比較。
方針：各段の定数 path の比較を極限の射へ束ねる。
規約：元の源の基礎単体集合の極限を使う。
使われ方：二つの極限の射による元の比較の因子分解。 -/
def mappingPathTowerLimitUnit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (dX n).right) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath (f n)).right)
        (fun n ↦ (mappingPathTowerStep X Y dX dY f hf n).right) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap (fun n ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit (f n)).right) (by
    intro n
    simpa only [Under.comp_right] using
      congrArg Under.Hom.right (mappingPathTower_unit_comm X Y dX dY f hf n))

/-- 概要：極限の定数 path の比較と源射影の合成は恒等射。
方針：各段の射影の後で元の切断の等式を使う。
規約：元の極限上で厳密に恒等射となる。
使われ方：全ての単射への RLP 射との合成から比較射の π_* 同型性を得る。 -/
lemma mappingPathTowerLimitUnit_source :
    mappingPathTowerLimitUnit X Y dX dY f hf ≫ mappingPathTowerLimitSource X Y dX dY f hf =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (dX n).right)) := by
  unfold mappingPathTowerLimitUnit mappingPathTowerLimitSource
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext
  intro n
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap_projection, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap_projection, Category.assoc]
  have h := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_retraction (f n))
  simp only [Under.comp_right, Under.id_right] at h
  rw [h, Category.comp_id, Category.id_comp]

/-- 概要：極限の定数 path の比較と終点射の合成は元の塔の極限の比較射。
方針：各段の射影の後で元の射の因子分解の等式を使う。
規約：各段の可換条件の証明の選択は合成を変えない。
使われ方：二つの全ての単射への RLP 射から元の極限の比較へ戻る。 -/
lemma mappingPathTowerLimitUnit_target :
    mappingPathTowerLimitUnit X Y dX dY f hf ≫ mappingPathTowerLimitTarget X Y dX dY f hf =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap (fun n ↦ (f n).right) (by
        intro n
        simpa only [Under.comp_right] using congrArg Under.Hom.right (hf n)) := by
  unfold mappingPathTowerLimitUnit mappingPathTowerLimitTarget
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext
  intro n
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap_projection, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap_projection, Category.assoc]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right)
    (fun n ↦ (dX n).right) n ≫ ·)
      (congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_projection (f n)))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
