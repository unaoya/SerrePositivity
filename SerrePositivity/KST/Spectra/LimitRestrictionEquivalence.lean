module

public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.JoinEquivalenceFunctor
public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting

/-!
概要：同値な形状の単射による錐の制限の相対充填。
方針：join の相対和の包含の前合成同値条件から、全ての境界で錐を厳密に延長する。
規約：図式の値域だけが quasicategory。一般化は K-Sp 所有内に置く。
使われ方：Kerodon §7.1、HTT 4.2.4.1。図式同値に沿う極限錐の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.DiagramLimitTransport

/-- 右因子が同値な join の相対和の包含は前合成同値条件を持つ。 -/
lemma joinUnion_right_equivalence {A K : SSet.{u}}
    (A₀ : A.Subcomplex) (K₀ : K.Subcomplex) (hK : IsPrecompositionEquivalence K₀.ι) :
    IsPrecompositionEquivalence (joinUnion A₀ K₀).ι := by
  have hright := (hK.joinMap_right (A₀ : SSet.{u})).of_isPushout (joinUnion_isPushout A₀ K₀)
  apply hright.cancel_left
  rw [joinUnionRight_ι]
  exact hK.joinMap_right A

/-- 概要：同値な部分図式への slice 制限は全ての単射の持ち上げを持つ。
方針：join の和に余錐を貼り、同値な単射の前合成で厳密に延長する。
規約：試験する部分複体には同値性を要求しない。使われ方：trivial Kan fibration の判定。 -/
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
  have hi := joinUnion_right_equivalence A₀ K₀ hK
  obtain ⟨v, hv⟩ := pre_surjective_of_essentiallySurjective (joinUnion A₀ K₀).ι
    (hi X).choose.isEssentiallySurjective (functorVertex T)
  let L := (functorVertexEquiv (join A K) X).symm v
  have hL : (joinUnion A₀ K₀).ι ≫ L = T := by
    apply functorVertex_injective
    change ((pre (joinUnion A₀ K₀).ι).app X).app (Opposite.op ⦋0⦌)
      (functorVertexEquiv (join A K) X L) = functorVertex T
    rw [Equiv.apply_symm_apply]
    exact hv
  have hleft : joinMap (𝟙 A) K₀.ι ≫ L = H := by
    rw [← joinUnionRight_ι A₀ K₀, Category.assoc]
    rw [hL]
    exact hs.inr_desc G H hover
  have hright : joinMap A₀.ι (𝟙 K) ≫ L = G := by
    rw [← joinUnionLeft_ι A₀ K₀, Category.assoc]
    rw [hL]
    exact hs.inl_desc G H hover
  have hfixed : joinInr A K ≫ L = p := by
    have hh := congrArg (fun z ↦ joinInr (A₀ : SSet.{u}) K ≫ z) hright
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceOverCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceOverUncurry_injective p
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact hright
  · apply sliceOverUncurry_injective (K₀.ι ≫ p)
    rw [sliceOverUncurry_restrict, sliceOverUncurry_curry]
    exact hleft


/-- 同値な部分図式への錐の制限は実際の trivial Kan fibration。 -/
lemma restriction_subcomplex_trivial {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (K₀ : K.Subcomplex) (hK : IsPrecompositionEquivalence K₀.ι) :
    TrivialKanFibration (sliceOverRestrict p K₀.ι) :=
  (trivialKanFibration_iff_boundary _).2
    (fun n ↦ sliceOverRestrict_lift_of_precompositionEquivalence p (boundary n) K₀ hK)

/-- 同値な任意の単射への錐の制限も実際の trivial Kan fibration。 -/
lemma restriction_trivial {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (f : L ⟶ K) [Mono f] (hf : IsPrecompositionEquivalence f) :
    TrivialKanFibration (sliceOverRestrict p f) := by
  let R : K.Subcomplex := Subfunctor.range f
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono f
  have hR : IsPrecompositionEquivalence R.ι :=
    (isPrecompositionEquivalence_of_iso (asIso (Subfunctor.toRange f))).cancel_left hf
  have hT := restriction_subcomplex_trivial p R hR
  have := sliceOverRestrict_isIso (R.ι ≫ p) (Subfunctor.toRange f)
  have he : f = Subfunctor.toRange f ≫ R.ι := rfl
  rw [he, sliceOverRestrict_comp]
  constructor
  exact trivialKanFibrations.comp_mem _ _ hT.mem (MorphismProperty.rlp_of_isIso _ _)

end SerrePositivity.KST.Spectra.DiagramLimitTransport
