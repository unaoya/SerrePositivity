module

public import SerrePositivity.KST.Spectra.SkeletalWeightedEndLimit
public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimit

/-!
概要：Kan 列の homotopy end の各段を有限骨格の end の塔の極限で表示する。
方針：Bousfield–Kan 重みの骨格の塔へ段ごとの係数図式を入力する。
規約：塔の各段の Kan 性と遷移の fibration 性は別途証明する。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。hG の各段の塔による解析。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet


namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 概要：homotopy end の段 k の有限骨格による塔。
方針：Bousfield–Kan 重みを骨格へ制限して点つき end を取る。
規約：k はスペクトルの段、塔の添字 n は重みに含める最大次元。
使われ方：Goerss–Jardine VIII §1。hG と homotopy Tot の有限段の解析。 -/
def homotopyEndLevelTower (D : I ⥤ KanSequence.{u}) (k : ℕ) :
    ℕᵒᵖ ⥤ PointedSimplicialSet.{u} :=
  SkeletalWeightedEnd.tower (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D k)

/-- 概要：homotopy end の段から有限骨格の塔への標準錐。
方針：重みの各骨格の包含で前合成する。
規約：錐の頂点は置換前の Kan end の実際の段。
使われ方：Goerss–Jardine VIII §1。hG の段ごとの制限族。 -/
def homotopyEndLevelCone (D : I ⥤ KanSequence.{u}) (k : ℕ) :
    Cone (homotopyEndLevelTower D k) :=
  SkeletalWeightedEnd.cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D k)

/-- 概要：homotopy end の各段の標準錐は有限骨格の塔の極限。
方針：重み付き end の骨格の塔の極限性を適用する。
規約：通常の点つき単体集合の極限。
使われ方：Goerss–Jardine VIII §1。π_* の塔の計算を各段へ戻す準備。 -/
def homotopyEndLevelConeIsLimit (D : I ⥤ KanSequence.{u}) (k : ℕ) :
    IsLimit (homotopyEndLevelCone D k) :=
  SkeletalWeightedEnd.coneIsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D k)

/-- 概要：実際の Kan end の段と有限骨格の塔の極限の同型。
方針：骨格の塔の標準の極限同型を使う。
規約：hG にも AsSmall を使う homotopy Tot にも適用できる。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。Kan 模型の厳密な復元。 -/
def homotopyEndLevelLimitIso (D : I ⥤ KanSequence.{u}) (k : ℕ) :
    ((homotopyLimit D).level k).space ≅ limit (homotopyEndLevelTower D k) :=
  SkeletalWeightedEnd.limitIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D k)

end

end SerrePositivity.KST.Spectra.KanSequence
