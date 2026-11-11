module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction

/-!
概要：任意の部分形状への slice の制限は right fibration である。
方針：右 anodyne な試験包含と形状の包含の pushout-join で錐を貼り、内充填する。
規約：形状の包含に anodyne 性は不要。使われ方：頂点固定の錐空間の制限の Kan 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 右 anodyne な試験包含は任意の部分形状への slice の制限に対し持ち上がる。 -/
lemma sliceOverRestrict_hasLiftingProperty_of_rightAnodyne {A K X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (A₀ : A.Subcomplex) (K₀ : K.Subcomplex)
    (hA : rightAnodyneExtensions A₀.ι) : HasLiftingProperty A₀.ι (sliceOverRestrict p K₀.ι) := by
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
  have hT : CommSq T (joinUnion A₀ K₀).ι (terminal.from X)
      (terminal.from (join A K)) := ⟨terminal.hom_ext _ _⟩
  have := joinUnion_innerAnodyne_of_rightAnodyne A₀ K₀ hA (terminal.from X) InnerFibration.mem
  let L := hT.lift
  have hleft : joinMap A₀.ι (𝟙 K) ≫ L = G := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft A₀ K₀ ≫ ((joinUnion A₀ K₀).ι ≫ hT.lift) = G
    rw [hT.fac_left]
    exact hs.inl_desc G H hover
  have hright : joinMap (𝟙 A) K₀.ι ≫ L = H := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight A₀ K₀ ≫ ((joinUnion A₀ K₀).ι ≫ hT.lift) = H
    rw [hT.fac_left]
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

/-- 任意の部分形状への slice の制限は right fibration。 -/
lemma sliceOverRestrict_subcomplex_rightFibration {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (K₀ : K.Subcomplex) : RightFibration (sliceOverRestrict p K₀.ι) where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hi =>
      exact sliceOverRestrict_hasLiftingProperty_of_rightAnodyne p (horn (n + 1) i) K₀
        (rightAnodyneExtensions_horn i hi)

end SerrePositivity.InfinityCategories.F2
