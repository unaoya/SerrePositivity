module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackAnodyneRestriction
public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativeLiftRestriction
public import SerrePositivity.InfinityCategories.F1.UniverseReflection

/-!
概要：全辺を覆う inner anodyne 部分底への、元の native Hom 制限の同値を選ぶ。
方針：元の制限の自明 Kan 性を同じ core 制限とその宇宙持ち上げへ移す。
規約：順方向は元の native 制限そのもの。部分底の充填性は要求しない。
使われ方：内ホーン上の実際の分類 Hom 比較を元の有限単体の作用から構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) [CocartesianFibration p] (q : F ⟶ nerve C)
  [CocartesianFibration q] (a : Over (nerve C))

local instance : InnerFibration (pullback.fst a.hom q) :=
  ⟨innerFibrations.pullback_fst a.hom q (InnerFibration.mem (q := q))⟩

/-- 全辺を覆う同じ inner anodyne 制限は、大きい宇宙の元の native core でも同値。 -/
lemma cocartesianAnodyneNativeLiftRestriction_isQCatEquivalence
    (ha : innerAnodyneExtensions a.hom)
    (he : Function.Surjective (a.hom.app (Opposite.op ⦋1⦌))) :
    IsQCatEquivalence (cocartesianPullbackNativeLiftRestriction p q a) := by
  letI := core_cocartesianPullbackNativeRestriction_trivialKanFibration p q a ha he
  exact (isQCatEquivalence_ulift_iff_of_kan _).mpr
    (isQCatEquivalence_of_trivialKanFibration _)

/-- 元の制限を順方向とする同値。逆射の選択を以降の比較で共有する。 -/
def cocartesianAnodyneNativeLiftRestrictionEquivalence
    (ha : innerAnodyneExtensions a.hom)
    (he : Function.Surjective (a.hom.app (Opposite.op ⦋1⦌))) :=
  (cocartesianAnodyneNativeLiftRestriction_isQCatEquivalence p q a ha he).choose

end SerrePositivity.InfinityCategories
