module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.Stability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.HomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangulatedInstance

/-! # 安定導来 ∞ 圏のホモトピー圏と D3 の比較

概要：安定性が三角構造を与える通常の h D(S) を、既存 D3 の二切断の表示へ接続する。
方針：辺の道の表示と辺の類の表示の比較同値を D3 と合成する。
規約：本モジュールでは三角関手性をまだ主張しない。使われ方：D7 の suspension・シフトの照合。
-/
@[expose] public section
noncomputable section
universe u w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories
open _root_.CategoryTheory _root_.SSet
variable (S : Type u) [CommRing S]

/-- 安定 ∞ 圏の三角構造が直接入る、道の商による h D(S)。 -/
abbrev derivedStableHomotopyCategory := hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)

/-- 通常の h D(S) と D3 の二切断による h D(S) の比較。 -/
def derivedStableHomotopyBridge :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S ≌ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).symm

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 安定性から三角構造を持つ h D(S) を通常の導来圏と比較する圏同値。 -/
def derivedStableHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S ≌ DerivedCategory (ModuleCat.{u} S) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyBridge S).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.1.12" (partial := special) "仮定：可換環 S と加群圏の導来圏の選択 HasDerivedCategory（Lean が強い：アーベル圏一般でなく加群圏の半自由複体模型）。結論：導来 ∞ 圏は安定で、ホモトピー圏と選んだ通常の導来圏が同値（一致）。"] _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence
attribute [cite HA "1.3.5.24" (partial := special) "仮定：通常のアーベル導来圏、∞ 圏側の比較は可換環上の加群（Lean が強い：一般の Grothendieck アーベル圏の二つの模型を扱わない）。結論：通常の圏で有界側の充満部分圏の包含、及び半自由模型の h の比較（Lean が弱い：射影模型から injective 模型への充満忠実性と指定された本質像は型にない）。"] _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence
attribute [cite HA "1.3.5.8" (partial := special) "仮定：可換環の加群。通常の圏との比較には HasDerivedCategory（Lean が強い：一般の Grothendieck アーベル圏を扱わない）。結論：半自由複体の dg nerve とその h の通常の導来圏との同値（Lean が弱い：injective 模型の dg nerve と準圏での比較がない）。"] _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence
