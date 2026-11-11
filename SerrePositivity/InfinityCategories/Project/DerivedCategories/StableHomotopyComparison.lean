module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Stability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.HomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangulatedInstance

/-! # 安定導来 ∞ 圏のホモトピー圏と D3 の比較

概要：安定性が三角構造を与える通常の h D(S) を、既存 D3 の二切断の表示へ接続する。
方針：辺の道の表示と辺の類の表示の比較同値を D3 と合成する。
規約：本モジュールでは三角関手性をまだ主張しない。使われ方：D7 の suspension・シフトの照合。
-/
@[expose] public section
noncomputable section
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
variable (S : Type u) [CommRing S]

/-- 安定 ∞ 圏の三角構造が直接入る、道の商による h D(S)。 -/
abbrev derivedStableHomotopyCategory := hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)

/-- 通常の h D(S) と D3 の二切断による h D(S) の比較。 -/
def derivedStableHomotopyBridge :
    derivedStableHomotopyCategory S ≌ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)).symm

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 安定性から三角構造を持つ h D(S) を通常の導来圏と比較する圏同値。 -/
def derivedStableHomotopyEquivalence :
    derivedStableHomotopyCategory S ≌ DerivedCategory (ModuleCat.{u} S) :=
  (derivedStableHomotopyBridge S).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
