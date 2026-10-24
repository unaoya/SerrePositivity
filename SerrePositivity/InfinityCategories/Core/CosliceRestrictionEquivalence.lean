module

public import SerrePositivity.InfinityCategories.Core.SliceUnderRestriction
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.JoinEquivalenceFunctor
public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting

/-! # 同値な形状による coslice の制限

概要：前合成の同値条件を持つ単射による図式の制限は、coslice の trivial Kan fibration を与える。
方針：join の pushout の片側の同値性を二対三則で他方へ移し、余錐の延長に使う。
規約：値域は quasicategory。使われ方：可逆円柱を通じた余極限の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左の形状が同値な join の相対的な和の包含は前合成の同値条件を持つ。
方針：左の join の同値性を pushout で保ち、全体の join との二対三則を使う。
規約：二つの部分複体を用いる。使われ方：coslice 制限の相対充填。 -/
lemma isPrecompositionEquivalence_joinUnion_left {A K : SSet.{u}}
    (K₀ : K.Subcomplex) (A₀ : A.Subcomplex) (hK : IsPrecompositionEquivalence K₀.ι) :
    IsPrecompositionEquivalence (joinUnion K₀ A₀).ι := by
  have hleft := (hK.joinMap_left (A₀ : SSet.{u})).of_isPushout (joinUnion_isPushout K₀ A₀).flip
  apply hleft.cancel_left
  rw [joinUnionLeft_ι]
  exact hK.joinMap_left A

/-- 概要：同値な部分図式への coslice 制限は全ての単射の持ち上げを持つ。
方針：join の和に余錐を貼り、同値な単射の前合成で厳密に延長する。
規約：試験する部分複体には同値性を要求しない。使われ方：trivial Kan fibration の判定。 -/
lemma sliceUnderRestrict_lift_of_precompositionEquivalence {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (K₀ : K.Subcomplex)
    (hK : IsPrecompositionEquivalence K₀.ι) :
    HasLiftingProperty A₀.ι (sliceUnderRestrict p K₀.ι) := by
  constructor
  intro a b sq
  let G := sliceUnderUncurry a
  let H := sliceUnderUncurry b
  have hover : joinMap K₀.ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 (K₀ : SSet.{u})) A₀.ι ≫ H := by
    have hh := congrArg sliceUnderUncurry sq.w
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp] at hh
    exact hh
  let hs := joinUnion_isPushout K₀ A₀
  let T := hs.desc H G hover.symm
  have hi := isPrecompositionEquivalence_joinUnion_left K₀ A₀ hK
  obtain ⟨v, hv⟩ := pre_surjective_of_essentiallySurjective (joinUnion K₀ A₀).ι
    (hi X).choose.isEssentiallySurjective (functorVertex T)
  let L := (functorVertexEquiv (join K A) X).symm v
  have hL : (joinUnion K₀ A₀).ι ≫ L = T := by
    apply functorVertex_injective
    change ((pre (joinUnion K₀ A₀).ι).app X).app (Opposite.op ⦋0⦌)
      (functorVertexEquiv (join K A) X L) = functorVertex T
    rw [Equiv.apply_symm_apply]
    exact hv
  have hleft : joinMap K₀.ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι K₀ A₀, Category.assoc]
    rw [hL]
    exact hs.inl_desc H G hover.symm
  have hright : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι K₀ A₀, Category.assoc]
    rw [hL]
    exact hs.inr_desc H G hover.symm
  have hfixed : joinInl K A ≫ L = p := by
    have hh := congrArg (fun z ↦ joinInl K (A₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hright
  · apply sliceUnderUncurry_injective (K₀.ι ≫ p)
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
    exact hleft


/-- 概要：同値な形状の部分複体への coslice 制限は trivial Kan fibration。
方針：全ての境界の持ち上げ性を適用する。
規約：値域は quasicategory。使われ方：可逆円柱の端点への制限。 -/
lemma sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence_subcomplex
    {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) (K₀ : K.Subcomplex)
    (hK : IsPrecompositionEquivalence K₀.ι) : TrivialKanFibration (sliceUnderRestrict p K₀.ι) :=
  (trivialKanFibration_iff_boundary _).2
    (fun n => sliceUnderRestrict_lift_of_precompositionEquivalence p (boundary n) K₀ hK)

/-- 概要：同値条件を持つ任意の単射への coslice 制限は trivial Kan fibration。
方針：像への同型と部分複体の包含に分解する。
規約：射の表示は任意。使われ方：可逆円柱の両端からの余錐の輸送。 -/
lemma sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence
    {K L X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K) [Mono f]
    (hf : IsPrecompositionEquivalence f) : TrivialKanFibration (sliceUnderRestrict p f) := by
  let R : K.Subcomplex := Subfunctor.range f
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono f
  have hR : IsPrecompositionEquivalence R.ι :=
    (isPrecompositionEquivalence_of_iso (asIso (Subfunctor.toRange f))).cancel_left hf
  have hT := sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence_subcomplex p R hR
  have he : f = Subfunctor.toRange f ≫ R.ι := rfl
  rw [he, ← sliceUnderRestrict_comp]
  constructor
  exact trivialKanFibrations.comp_mem _ _ hT.mem (MorphismProperty.rlp_of_isIso _ _)

end SerrePositivity.InfinityCategories
