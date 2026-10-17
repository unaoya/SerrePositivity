module

public import SerrePositivity.InfinityCategories.Core.NerveCone

/-!
概要：始対象を持つ通常の圏の図式上の slice の、始対象での値への制限。
方針：始対象の頂点包含の left anodyne 性と A2c による slice の制限の充填性を使う。
規約：文言と向きは実装前に Core/README.md に固定したもの。
使われ方：HTT §4.1.1 の必要な場合、Kerodon §7.2.2 と Corollary 4.3.6.14。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories

/-- 概要：通常の圏上の図式の slice を指定対象での値上の slice へ制限する。
方針：その対象の nerve への頂点包含で図式を前合成する。
規約：向きは全図式上の slice から値上の slice。
使われ方：HTT §4.1.1、Kerodon §7.2.2 の始対象による制限。 -/
def initialRestriction {I : Type u} [Category.{u} I] {X : SSet.{u}}
    (F : nerve I ⟶ X) (c : I) : sliceOver F ⟶ sliceOver (nervePoint c ≫ F) :=
  sliceOverRestrict F (nervePoint c)

/-- 概要：始対象を持つ小圏上の図式の slice の始対象への制限は trivial Kan fibration。
方針：始対象の頂点包含が left anodyne であることと、slice の制限の一般補題を使う。
規約：F は任意の単体集合の射であり、圏の関手の nerve であることを要求しない。
使われ方：HTT §4.1.1 の必要な場合、Kerodon §7.2.2・Corollary 4.3.6.14。 -/
lemma initialCofinality {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c)
    {X : SSet.{u}} [Quasicategory X] (F : nerve I ⟶ X) :
    TrivialKanFibration (initialRestriction F c) :=
  sliceOverRestrict_trivialKanFibration F (nervePoint c) (nervePoint_leftAnodyne hc)

end SerrePositivity.InfinityCategories
