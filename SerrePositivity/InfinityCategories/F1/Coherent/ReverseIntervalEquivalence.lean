module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingReverseIso
public import SerrePositivity.InfinityCategories.F1.Coherent.ReverseTransportComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence

/-!
概要：反転した coherent 合成の底の区間パラメーター比較の同値性。
方針：curry した比較を右 Hom の区間比較の反転と区間写像空間の反転同型に分解する。
規約：局所 Kan 性以外の仮定を加えない。
使われ方：普遍輸送の比較で底のパラメーター比較を消去する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：反転した Hom の区間族を固定端点の区間写像空間への射にする。
方針：既証明の端点公式で curry する。
規約：始域は豊穣 Hom の ULift の反転。
使われ方：反転した標準合成と普遍輸送に共通するパラメーター射。 -/
def coherentReverseHomIntervalMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op ⟶
      intervalMappingSpace (SSet.opObjEquiv.symm (coherentNerveVertex Y))
        (SSet.opObjEquiv.symm (coherentNerveVertex X)) :=
  intervalMappingCurryOfEndpoints (coherentReverseHomInterval X Y)
    (coherentReverseHomInterval_zero X Y) (coherentReverseHomInterval_one X Y)

/-- 概要：反転した Hom の区間パラメーター射は既存の区間比較の反転と反転同型の合成。
方針：区間族の反転の自然性を普遍的な Hom の族に適用する。
規約：射そのものの厳密な等式。
使われ方：反転した底のパラメーター比較の同値性の証明。 -/
lemma coherentReverseHomIntervalMap_eq {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    coherentReverseHomIntervalMap X Y =
      SSet.opFunctor.map (coherentHomComparison X Y ≫ pinchedHomToIntervalMappingSpace _ _) ≫
        intervalMappingReverse (coherentNerveVertex X) (coherentNerveVertex Y) := by
  change intervalMappingReverseFamily
    (coherentHomComparison X Y ≫ pinchedHomToIntervalMappingSpace _ _) = _
  exact intervalMappingReverseFamily_eq _

/-- 概要：反転した coherent Hom の底の区間パラメーター射は同値。
方針：右 Hom 比較と区間比較の同値を反転し、区間写像空間の厳密な反転同型を合成する。
規約：全ての豊穣 Hom の Kan 性だけを要求する。
使われ方：普遍輸送の全写像空間上の同値性へ標準合成の同値性を移す。 -/
lemma coherentReverseHomIntervalMap_isQCatEquivalence {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ A B : C, KanComplex (SimplicialCategory.sHom A B)]
    (X Y : C) : IsQCatEquivalence (coherentReverseHomIntervalMap X Y) := by
  rw [coherentReverseHomIntervalMap_eq]
  have h₀ := (coherentHomComparison_isQCatEquivalence X Y).comp
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence (coherentNerveVertex X)
      (coherentNerveVertex Y))
  have h₁ := HomotopyLimits.oppositeKanHomotopyEquivalence h₀.isSimplicialHomotopyEquivalence
  exact h₁.isQCatEquivalence.comp
    (qCatEquivalenceOfIso (intervalMappingReverseIso (coherentNerveVertex X)
      (coherentNerveVertex Y))).isQCatEquivalence

end SerrePositivity.InfinityCategories
