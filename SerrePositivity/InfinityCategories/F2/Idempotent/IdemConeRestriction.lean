module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemLeftCofinality
public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.LimitConeExtension

/-!
概要：元の冪等包含への錐制限は自明 Kan で、同じ錐の極限性を保ち反映する。
方針：元の単射な包含の left cofinal 性を left anodyne 性へ移す。
規約：指定した元の全錐を同じ包含で制限する。
使われ方：HTT 4.4.5.13 の元の強い分裂からの錐の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の冪等包含そのものは left anodyne でもある。 -/
lemma idemInclusion_leftAnodyne : leftAnodyneExtensions idemInclusion.{u} :=
  idemInclusion_isLeftCofinal.leftAnodyneExtensions

/-- 元の全強分裂図式に沿った錐を元の Idem へ制限する射は自明 Kan。 -/
lemma idemConeRestriction_trivialKanFibration {X : SSet.{u}} [Quasicategory X]
    (F : SplitShape ⟶ X) : TrivialKanFibration (sliceOverRestrict F idemInclusion) :=
  sliceOverRestrict_trivialKanFibration F idemInclusion idemInclusion_leftAnodyne

/-- 元の全強分裂図式の指定錐の極限性は、元の Idem への制限で判定できる。 -/
lemma idemCone_isLimit_iff_restrict {X : SSet.{u}} [Quasicategory X]
    {F : SplitShape ⟶ X} (c : JoinCone F) :
    IsLimitCone c ↔ IsLimitCone (F2.restrictJoinCone c idemInclusion) := by
  have := idemConeRestriction_trivialKanFibration F
  exact (qCatEquivalenceOfTrivialKanFibration
    (sliceOverRestrict F idemInclusion)).isTerminalVertex_iff c

end SerrePositivity.InfinityCategories.F2.Idempotent
