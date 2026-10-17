module

public import SerrePositivity.InfinityCategories.Core.SliceRestriction

/-!
概要：図式の部分複体への coslice の制限の左ファイブレーション性。
方針：左 anodyne 射との pushout-join を使い、錐を貼り合わせて延長する。
規約：制限する部分複体の包含には anodyne 性を要求しない。
使われ方：Kerodon Corollary 4.3.6.14、Proposition 4.4.2.13、HTT §2.1.2。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coslice の部分図式への制限は左 anodyne な包含の rlp を持つ。
方針：二つの錐を pushout-join 上で貼り合わせ、内 anodyne 性と X の充填を使う。
規約：K₀ は任意の部分複体。
使われ方：Kerodon Corollary 4.3.6.14、HTT §2.1.2 の制限の充填。 -/
lemma sliceUnderRestrict_hasLiftingProperty {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (K₀ : K.Subcomplex)
    (hA : leftAnodyneExtensions A₀.ι) : HasLiftingProperty A₀.ι (sliceUnderRestrict p K₀.ι) := by
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
  have hT : CommSq T (joinUnion K₀ A₀).ι (terminal.from X)
      (terminal.from (join K A)) := ⟨terminal.hom_ext _ _⟩
  have := joinUnion_innerAnodyne_of_leftAnodyne K₀ A₀ hA (terminal.from X) InnerFibration.mem
  let L := hT.lift
  have hleft : joinMap K₀.ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ hT.lift) = H
    rw [hT.fac_left]
    exact hs.inl_desc H G hover.symm
  have hright : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ hT.lift) = G
    rw [hT.fac_left]
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

/-- 概要：coslice の任意の部分図式への制限は左ファイブレーション。
方針：前の補題を全ての左ホーンに適用する。
規約：標的 X は quasicategory。
使われ方：Kerodon Corollary 4.3.6.14、Proposition 4.4.2.13 の可逆な辺の持ち上げ。 -/
instance sliceUnderRestrict_leftFibration {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (K₀ : K.Subcomplex) : LeftFibration (sliceUnderRestrict p K₀.ι) where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hi =>
      exact sliceUnderRestrict_hasLiftingProperty p (horn (n + 1) i) K₀
        (leftAnodyneExtensions_horn i hi)

end SerrePositivity.InfinityCategories
