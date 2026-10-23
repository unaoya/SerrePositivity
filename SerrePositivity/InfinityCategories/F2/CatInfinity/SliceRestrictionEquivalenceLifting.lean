module

public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.JoinEquivalenceFunctor
public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting

/-!
概要：同値な部分図式への slice 制限の相対的な充填。
方針：join の和を使い、同値な形状の前合成に沿って錐を延長する。
規約：全ての試験部分複体について充填する。
使われ方：Cat_∞ の図式同型に沿う極限錐の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：join の右の部分図式が同値なら相対的な和の包含も前合成同値。
方針：右の join 同値を pushout で保ち、全体の join との二対三則を使う。
規約：左の試験部分複体には同値性を要求しない。
使われ方：slice の制限に対する任意の境界の充填。 -/
lemma isPrecompositionEquivalence_joinUnion_right {A K : SSet.{u}}
    (A₀ : A.Subcomplex) (K₀ : K.Subcomplex) (hK : IsPrecompositionEquivalence K₀.ι) :
    IsPrecompositionEquivalence (joinUnion A₀ K₀).ι := by
  have hright := (hK.joinMap_right (A₀ : SSet.{u})).of_isPushout (joinUnion_isPushout A₀ K₀)
  apply hright.cancel_left
  rw [joinUnionRight_ι]
  exact hK.joinMap_right A
/-- 概要：同値な部分図式への slice 制限は全ての部分複体包含の持ち上げを持つ。
方針：join の和に二つの錐を貼り、前合成同値に沿って厳密に延長する。
規約：標的は quasicategory、二つの部分複体は任意。
使われ方：同値な形状への slice 制限の trivial Kan fibration 性。 -/
lemma sliceOverRestrict_lift_of_precompositionEquivalence {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (K₀ : K.Subcomplex)
    (hK : IsPrecompositionEquivalence K₀.ι) :
    HasLiftingProperty A₀.ι (sliceOverRestrict p K₀.ι) := by
  constructor
  intro a b sq
  let G := sliceOverUncurry a
  let H := sliceOverUncurry b
  have hover : joinMap (𝟙 (A₀ : SSet.{u})) K₀.ι ≫ G =
      joinMap A₀.ι (𝟙 (K₀ : SSet.{u})) ≫ H := by
    have hh := congrArg sliceOverUncurry sq.w
    rw [sliceOverUncurry_restrict, sliceOverUncurry_precomp] at hh
    exact hh
  let hs := joinUnion_isPushout A₀ K₀
  let T := hs.desc G H hover
  have hi := isPrecompositionEquivalence_joinUnion_right A₀ K₀ hK
  obtain ⟨v, hv⟩ := pre_surjective_of_essentiallySurjective (joinUnion A₀ K₀).ι
    (hi X).choose.isEssentiallySurjective (functorVertex T)
  let L := (functorVertexEquiv (join A K) X).symm v
  have hL : (joinUnion A₀ K₀).ι ≫ L = T := by
    apply functorVertex_injective
    change ((pre (joinUnion A₀ K₀).ι).app X).app (Opposite.op ⦋0⦌)
      (functorVertexEquiv (join A K) X L) = functorVertex T
    rw [Equiv.apply_symm_apply]
    exact hv
  have hleft : joinMap A₀.ι (𝟙 K) ≫ L = G := by
    rw [← joinUnionLeft_ι, Category.assoc]
    rw [hL]
    exact hs.inl_desc G H hover
  have hright : joinMap (𝟙 A) K₀.ι ≫ L = H := by
    rw [← joinUnionRight_ι, Category.assoc]
    rw [hL]
    exact hs.inr_desc G H hover
  have hfixed : joinInr A K ≫ L = p := by
    have hh := congrArg (fun z ↦ joinInr (A₀ : SSet.{u}) K ≫ z) hleft
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceOverCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceOverUncurry_injective p
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact hleft
  · apply sliceOverUncurry_injective (K₀.ι ≫ p)
    rw [sliceOverUncurry_restrict, sliceOverUncurry_curry]
    exact hright


end SerrePositivity.InfinityCategories.F2
