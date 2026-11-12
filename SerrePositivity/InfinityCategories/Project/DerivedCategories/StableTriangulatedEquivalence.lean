module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StableHomotopyTriangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # 安定導来 ∞ 圏の h と導来圏の三角同値

概要：D3 の圏同値を、実際の cofiber による三角構造の三角同値へ昇格する。
方針：実 suspension のシフト比較を逆関手へ移し、三角随伴の一般論を適用する。
規約：両側の全整数シフトと単位・余単位の整合性を含む。使われ方：D7 の完了界面。
-/
@[expose] public section
noncomputable section
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Pretriangulated
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- D3 の逆関手の整合的な整数シフト比較。 -/
instance derivedStableHomotopyEquivalenceInverseCommShift :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).inverse.CommShift ℤ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).commShiftInverse ℤ

/-- D3 の単位・余単位は両関手の整数シフト比較と整合する。 -/
instance derivedStableHomotopyEquivalenceCommShiftCompatible :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).CommShift ℤ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).commShift_of_functor ℤ

/-- D3 は安定 ∞ 圏の実 cofiber による三角構造に関する三角同値。 -/
instance derivedStableHomotopyEquivalenceIsTriangulated :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ inferInstance

/-- D3 の逆関手も distinguished triangle を保存する。 -/
lemma derivedStableHomotopyInverse_map_distinguished
    (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat S)))
    (hT : T ∈ distTriang _) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).inverse.mapTriangle.obj T ∈
      distTriang (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyCategory S) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).inverse.map_distinguished T hT

end SerrePositivity.InfinityCategories.Project.DerivedCategories
