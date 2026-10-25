module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFilteredColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceAccessibleTerminal
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleEquivalence

/-!
概要：固定始域圏の未解決の accessibility を、元の始点評価の通常の点引き戻しに揃える。
方針：構成済みの全脚族を保持する同値で、同じ濃度の生成表示を輸送する。
規約：引き戻しの accessibility は入力に明示し、その存在は主張しない。
使われ方：e5 の点 fiber の filtered 生成表示と f3 の終対象構成を接続する境界。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 点引き戻しの生成表示は、濃度を変えずに固定始域の元の coslice 部分圏へ戻る。 -/
lemma generatedSource_isKappaAccessible_iff_pointPullback (κ : Cardinal.{u})
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    IsKappaAccessible κ (generatedSourceCategory edges x) ↔
      IsKappaAccessible κ (generatedSourcePointPullback edges x) :=
  isKappaAccessible_iff_equivalence (generatedSourcePointPullbackEquivalence edges x)

/-- 点 fiber と元の固定始域圏の accessibility は同値である。 -/
lemma generatedSource_isAccessible_iff_pointPullback
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    IsAccessible (generatedSourceCategory edges x) ↔
      IsAccessible (generatedSourcePointPullback edges x) :=
  isAccessible_iff_equivalence (generatedSourcePointPullbackEquivalence edges x)

/-- 未解決の点 fiber の accessibility から、元の始点を保持する局所置換へ接続する。 -/
lemma exists_generatedSource_localReplacement_of_accessiblePointPullback
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (ha : IsAccessible (generatedSourcePointPullback edges x)) :
    ∃ (y : C _⦋0⦌) (e : C.Edge x y),
      e.edge ∈ generatedEdges edges ∧ IsLocalObject (Set.range edges) y :=
  exists_generatedSource_localReplacement_of_isAccessible hC edges x
    ((generatedSource_isAccessible_iff_pointPullback edges x).mpr ha)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
