module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.EquivalenceLifting
public import SerrePositivity.InfinityCategories.Core.CosliceRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceRestrictionIso

/-!
概要：同値な単射上の相対 coslice 制限は isofibration の上で自明 Kan。
方針：join の和の単射な前合成同値を右に持ち上げ、部分錐と底の錐を同時に延長する。
規約：元と標的の図式を厳密に保つ。
使われ方：標準局所添字から comma fiber へ像を保って余錐を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：同値な部分図式への相対 coslice 制限は任意の部分複体を持ち上げる。
方針：部分錐と像の錐を join の和で貼り、単射な前合成同値に対する持ち上げを使う。
規約：試験パラメータと図式の添字には quasicategory 性を要求しない。
使われ方：相対 coslice 制限の全境界充填。 -/
lemma kanRelativeCosliceMap_lift_of_precompositionEquivalence {A K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (hq : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting q)
    (A₀ : A.Subcomplex) (K₀ : K.Subcomplex) (hK : IsPrecompositionEquivalence K₀.ι) :
    HasLiftingProperty A₀.ι (relativeCosliceMap p q K₀) := by
  constructor
  intro a b sq
  let r := pullback.fst (sliceUnderPostcomp (K₀.ι ≫ p) q)
    (sliceUnderRestrict (p ≫ q) K₀.ι)
  let s := pullback.snd (sliceUnderPostcomp (K₀.ι ≫ p) q)
    (sliceUnderRestrict (p ≫ q) K₀.ι)
  let G := sliceUnderUncurry a
  let H := sliceUnderUncurry (b ≫ r)
  let B := sliceUnderUncurry (b ≫ s)
  have ha : a ≫ sliceUnderRestrict p K₀.ι = A₀.ι ≫ (b ≫ r) := by
    have h := congrArg (fun f ↦ f ≫ r) sq.w
    simpa only [r, relativeCosliceMap, Category.assoc, pullback.lift_fst] using h
  have hb : a ≫ sliceUnderPostcomp p q = A₀.ι ≫ (b ≫ s) := by
    have h := congrArg (fun f ↦ f ≫ s) sq.w
    simpa only [s, relativeCosliceMap, Category.assoc, pullback.lift_snd] using h
  have hover : joinMap K₀.ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 (K₀ : SSet.{u})) A₀.ι ≫ H := by
    have h := congrArg sliceUnderUncurry ha
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp] at h
    exact h
  let hs := joinUnion_isPushout K₀ A₀
  let T := hs.desc H G hover.symm
  have hTB : T ≫ q = (joinUnion K₀ A₀).ι ≫ B := by
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc, ← Category.assoc, joinUnionLeft_ι]
      have h : (b ≫ r) ≫ sliceUnderPostcomp (K₀.ι ≫ p) q =
          (b ≫ s) ≫ sliceUnderRestrict (p ≫ q) K₀.ι := by
        simpa only [r, s, Category.assoc] using congrArg (fun z ↦ b ≫ z)
          (pullback.condition (f := sliceUnderPostcomp (K₀.ι ≫ p) q)
            (g := sliceUnderRestrict (p ≫ q) K₀.ι))
      have hh := congrArg sliceUnderUncurry h
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_restrict] at hh
      exact hh
    · rw [← Category.assoc, hs.inr_desc, ← Category.assoc, joinUnionRight_ι]
      have h := congrArg sliceUnderUncurry hb
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at h
      exact h
  have := hq (joinUnion K₀ A₀).ι inferInstance
    (isPrecompositionEquivalence_joinUnion_left K₀ A₀ hK)
  let hT : CommSq T (joinUnion K₀ A₀).ι q B := ⟨hTB⟩
  let L := hT.lift
  have hleft : joinMap K₀.ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ hT.lift) = H
    rw [hT.fac_left]
    exact hs.inl_desc _ _ _
  have hright : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ hT.lift) = G
    rw [hT.fac_left]
    exact hs.inr_desc _ _ _
  have hfixed : joinInl K A ≫ L = p := by
    have h := congrArg (fun z ↦ joinInl K (A₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    exact h.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hright
  · apply pullback.hom_ext
    · change sliceUnderCurry L hfixed ≫ relativeCosliceMap p q K₀ ≫ r = b ≫ r
      have hr : relativeCosliceMap p q K₀ ≫ r = sliceUnderRestrict p K₀.ι :=
        pullback.lift_fst _ _ _
      rw [hr]
      apply sliceUnderUncurry_injective (K₀.ι ≫ p)
      rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
      exact hleft
    · change sliceUnderCurry L hfixed ≫ relativeCosliceMap p q K₀ ≫ s = b ≫ s
      have hs : relativeCosliceMap p q K₀ ≫ s = sliceUnderPostcomp p q :=
        pullback.lift_snd _ _ _
      rw [hs]
      apply sliceUnderUncurry_injective (p ≫ q)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
      exact hT.fac_right

/-- 概要：同値な部分図式への相対 coslice 制限は自明 Kan。
方針：全境界に部分余錐・元の図式・底の錐を保つ延長を適用する。
規約：q には単射な前合成同値の右持ち上げ条件を課す。
使われ方：同値な添字変更で像を保って余錐を延長する。 -/
lemma kanRelativeCosliceMap_trivialKanFibration_of_precompositionEquivalence
    {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y) (hq : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting q)
    (K₀ : K.Subcomplex) (hK : IsPrecompositionEquivalence K₀.ι) :
    TrivialKanFibration (relativeCosliceMap p q K₀) :=
  (trivialKanFibration_iff_boundary _).2 (fun n ↦
    kanRelativeCosliceMap_lift_of_precompositionEquivalence p q hq (boundary n) K₀ hK)

/-- 概要：任意表示の同値な単射への相対 coslice 制限も自明 Kan。
方針：単射を像への同型と部分複体包含に分解し、相対制限の合成で戻す。
規約：添字の射の表示や quasicategory 性は制限しない。
使われ方：標準局所形から comma fiber への単射な前合成同値に適用する。 -/
lemma kanRelativeCosliceRestriction_trivialKanFibration_of_precompositionEquivalence
    {K L X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y) (hq : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting q)
    (i : L ⟶ K) [Mono i] (hi : IsPrecompositionEquivalence i) :
    TrivialKanFibration (relativeCosliceRestriction p q i) := by
  let R : K.Subcomplex := Subfunctor.range i
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono i
  have hR : IsPrecompositionEquivalence R.ι :=
    (isPrecompositionEquivalence_of_iso (asIso (Subfunctor.toRange i))).cancel_left hi
  have := kanRelativeCosliceMap_trivialKanFibration_of_precompositionEquivalence p q hq R hR
  exact relativeCosliceRestriction_trivialKanFibration_subcomplexIso p q R
    (asIso (Subfunctor.toRange i))

end SerrePositivity.InfinityCategories.F1B
