module

public import SerrePositivity.InfinityCategories.F1B.KanSectionLeftIntervalEquivalence
public import SerrePositivity.InfinityCategories.F1B.PinchedIntervalEquivalence

/-!
概要：既存の右 pinched 区間比較を左 coslice の比較と接続する。
方針：F1b の証明済み比較と、同じ図式を表す区間比較の一致を使う。
規約：右模型の証明を再実装しない。
使われ方：区間上の cocartesian 比較による全空間の同値判定。
-/
@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.KanSection
/-- 概要：右 pinched 模型の既存の区間比較は ∞ 圏同値。
方針：F1b の右比較と展開後に一致することを確認する。
規約：比較射そのものの同値性を示す。
使われ方：coslice の後合成の写像空間条件への移送。 -/
lemma pinchedHomToIntervalMappingSpace_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    IsQCatEquivalence (pinchedHomToIntervalMappingSpace x y) := by
  have he : PinchedInterval.comparison x y = pinchedHomToIntervalMappingSpace x y := by
    apply intervalMappingUncurry_injective
    have hl := PinchedInterval.comparison_uncurry (𝟙 (pinchedHom x y))
    have hr := pinchedHomToIntervalMappingSpace_uncurry (𝟙 (pinchedHom x y))
    simpa only [Category.id_comp] using hl.trans hr.symm
  rw [← he]
  exact PinchedInterval.comparison_isQCatEquivalence x y
end SerrePositivity.InfinityCategories.KanSection
