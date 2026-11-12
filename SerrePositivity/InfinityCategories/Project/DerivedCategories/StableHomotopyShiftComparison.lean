module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SuspensionShiftNaturalIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ShiftCommutationInteger

/-! # 安定性からの整数シフトと D3 の整合性

概要：通常の h D(S) の安定構造の整数シフトと、通常の導来圏のシフトを D3 で比較する。
方針：実際の suspension の自然同型を一回シフトへ移し、整合的な整数冪へ延長する。
規約：元の D3 の二切断上の誘導シフトと区別する。使われ方：D7 の三角関手性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 安定構造の一回シフトと D3 比較の交換同型。 -/
def derivedStableHomotopyShiftOneIso :
    shiftFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyCategory S) (1 : ℤ) ⋙
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor ⋙ shiftFunctor _ (1 : ℤ) :=
  Functor.isoWhiskerRight (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftIso S

/-- 通常の h の D3 比較は安定構造の全整数シフトと整合的に交換する。 -/
instance derivedStableHomotopyEquivalenceCommShift :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.CommShift ℤ :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableCommShiftOfOne (derivedStableHomotopyShiftOneIso S)

/-- 全整数の比較は構成した実際の一回シフト比較を厳密に復元する。 -/
lemma derivedStableHomotopyEquivalenceCommShift_one :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.commShiftIso (1 : ℤ) =
      derivedStableHomotopyShiftOneIso S :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableCommShiftOfOne_one (derivedStableHomotopyShiftOneIso S)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
