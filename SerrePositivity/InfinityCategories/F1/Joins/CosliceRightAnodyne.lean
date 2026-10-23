module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.CosliceConverse

/-!
概要：右 anodyne な部分図式への相対 coslice 制限の充填。
方針：右 anodyne な左因子と任意の右因子の pushout-join を使う。
規約：対象側の図式は固定し、底の全ての錐を厳密に保つ。
使われ方：Kerodon Proposition 4.3.6.14、Proposition 5.2.5.1 の三角形への制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右 anodyne な部分図式への相対 coslice 制限は任意の部分複体包含を持ち上げる。
方針：二つの錐を pushout-join に貼り、inner fibration の充填を適用する。
規約：試験する部分複体 A₀ に anodyne 性は不要。
使われ方：Kerodon Proposition 4.3.6.14、相対的な三角形の錐の延長。 -/
lemma relativeCosliceMap_lift_of_rightAnodyne {A K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (A₀ : A.Subcomplex) (K₀ : K.Subcomplex) (hK : rightAnodyneExtensions K₀.ι) :
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
  have := joinUnion_innerAnodyne_of_rightAnodyne K₀ A₀ hK q (InnerFibration.mem (q := q))
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

/-- 概要：右 anodyne な部分図式への相対 coslice 制限は trivial Kan fibration。
方針：全境界の持ち上げ性で判定する。
規約：quasicategory 性を追加で仮定しない。
使われ方：Kerodon Proposition 4.3.6.14、Proposition 5.2.5.1 の錐の制限。 -/
lemma relativeCosliceMap_trivialKanFibration_of_rightAnodyne {K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (K₀ : K.Subcomplex) (hK : rightAnodyneExtensions K₀.ι) :
    TrivialKanFibration (relativeCosliceMap p q K₀) :=
  (trivialKanFibration_iff_boundary _).2
    (fun n ↦ relativeCosliceMap_lift_of_rightAnodyne p q (boundary n) K₀ hK)

end SerrePositivity.InfinityCategories
