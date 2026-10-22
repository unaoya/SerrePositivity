module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionCosliceTrivial
public import SerrePositivity.InfinityCategories.F1B.QuillenA

/-!
概要：trivial Kan 射影の任意の厳密な切断は right cofinal。
方針：同じ切断の各 coslice を、底の弱可縮な coslice と trivial Kan 射影で比較する。
規約：切断を別の逆射へ取り替えず、同値性を追加仮定にしない。
使われ方：保存済みの包含順の nerve からの写像自体の cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ trivial Kan 射影の同じ厳密な切断に Quillen A を適用する。 -/
lemma isRightCofinal_section_of_trivialKanFibration {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [TrivialKanFibration p] (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) :
    IsRightCofinal s := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  apply isRightCofinal_of_weaklyContractible_coslices
  intro e
  let a := SSet.yonedaEquiv.symm e
  have := sectionCosliceMap_trivialKanFibration a p s hs
  have hw :=
    (isRightCofinal_of_trivialKanFibration (sectionCosliceMap a p s)).isWeakHomotopyEquivalence
  apply hw.weaklyContractible_iff.mpr
  have hb := sliceUnder_isWeaklyContractible (SSet.yonedaEquiv (a ≫ p))
  simpa only [SSet.yonedaEquiv.symm_apply_apply] using hb

end SerrePositivity.InfinityCategories.F2.Ind
