module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinInitialComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
/-!
概要：任意の空添字の図式の slice は、元の標的と厳密に同型。
方針：join の単位同型と Yoneda の全単射を、各次数の射影に適用する。
規約：空添字の特定の表示に依存しない。使われ方：相対 slice の空部分を元の圏へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
/-- 空添字上の任意の図式の slice 射影は、全次数で厳密な同型。 -/
lemma initialIndexSliceProjection_isIso {K X : SSet.{u}} (hK : IsInitial K) (p : K ⟶ X) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isIso_joinInl_of_isInitial (Δ[n] : SSet.{u}) K hK
  rw [isIso_iff_bijective]
  constructor
  · intro a b h
    apply Subtype.ext
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) K)).1
    exact SSet.yonedaEquiv.injective h
  · intro x
    refine ⟨⟨inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) K) ≫ SSet.yonedaEquiv.symm x,
      hK.hom_ext _ _⟩, ?_⟩
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) K ≫
      (inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) K) ≫ SSet.yonedaEquiv.symm x)) = x
    rw [IsIso.hom_inv_id_assoc, SSet.yonedaEquiv.apply_symm_apply]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
