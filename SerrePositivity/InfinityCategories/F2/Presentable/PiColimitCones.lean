module

public import SerrePositivity.InfinityCategories.F2.Presentable.PiQuasicategory
public import SerrePositivity.InfinityCategories.Core.ConeOpposite
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceColimits

/-!
概要：小さい全直積の余錐を成分ごとに組み立てる。
方針：元の coslice を成分の coslice の全直積へ同定し、境界充填をまとめる。
規約：添字の有限性も形状の充填性も要求しない。
使われ方：presentable 圏の小さい積の余完備性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全成分が始対象なら、元の全直積の同じ頂点も始対象。
方針：指定境界の各成分の充填を全直積へまとめる。
規約：成分の quasicategory 性は要求しない。
使われ方：直積余錐の普遍性。 -/
lemma piSSet_isInitialVertex {ι : Type u} {C : ι → SSet.{u + 1}}
    (x : (piSSet C) _⦋0⦌) (h : ∀ i, IsInitialVertex (x i)) : IsInitialVertex x := by
  intro n b hb
  have hi (i : ι) : boundaryVertex n 0 ≫ (b ≫ piSSetProjection C i) =
      SSet.yonedaEquiv.symm (x i) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  choose f hf using fun i ↦ h i n (b ≫ piSSetProjection C i) (hi i)
  refine ⟨piSSetLift f, ?_⟩
  apply piSSet_hom_ext
  intro i
  simpa only [Category.assoc, piSSetLift_projection] using hf i

/-- 概要：成分の全余錐を元の直積内の全余錐へ貼り合わせる写像。
方針：各単体を join からの全射としてまとめる。
規約：同じ元の図式を固定する。
使われ方：直積の coslice の厳密な比較。 -/
def piSliceUnderGlue {ι : Type u} {C : ι → SSet.{u + 1}} {J : SSet.{u + 1}}
    (p : J ⟶ piSSet C) :
    piSSet (fun i ↦ sliceUnder (p ≫ piSSetProjection C i)) ⟶ sliceUnder p where
  app _ := ↾fun s ↦ ⟨piSSetLift (fun i ↦ (s i).val), by
    apply piSSet_hom_ext
    intro i
    simpa only [Category.assoc, piSSetLift_projection] using (s i).property⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply piSSet_hom_ext
    intro i
    rfl

/-- 概要：元の直積図式の全 coslice は全成分の coslice の直積と同型。
方針：元の射影による後合成と、全余錐の貼り合わせを逆にする。
規約：全高次の余錐を保持する。
使われ方：小さい全直積内の成分ごとの余極限構成。 -/
def piSliceUnderIso {ι : Type u} {C : ι → SSet.{u + 1}} {J : SSet.{u + 1}}
    (p : J ⟶ piSSet C) :
    sliceUnder p ≅ piSSet (fun i ↦ sliceUnder (p ≫ piSSetProjection C i)) where
  hom := piSSetLift (fun i ↦ sliceUnderPostcomp p (piSSetProjection C i))
  inv := piSliceUnderGlue p
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply piSSet_hom_ext
    intro i
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    funext i
    apply Subtype.ext
    rfl

/-- 概要：全成分で余極限となる元の直積内の余錐は余極限。
方針：coslice の同型と成分の始対象の境界充填を使う。
規約：元の指定全余錐自身を判定する。
使われ方：小さい積の全小余極限の構成。 -/
lemma piSSet_isColimitCone_of_components {ι : Type u} {C : ι → SSet.{u + 1}}
    {J : SSet.{u + 1}} {p : J ⟶ piSSet C} (c : JoinCocone p)
    (h : ∀ i, IsColimitCone (mapJoinCocone (piSSetProjection C i) c)) :
    IsColimitCone c := by
  apply (isInitialVertex_iff_of_isIso (piSliceUnderIso p).hom c).mpr
  apply piSSet_isInitialVertex
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
