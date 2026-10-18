module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CospanCornerTensor

/-!
概要：一脚の fibration 性の下での相対境界が anodyne な重みの制限。
方針：境界との pushout-product の相対境界を交換同型で移し、一脚の相対延長へ渡す。
規約：具体的な重みの中央の相対境界の anodyne 性は別の入力として明示する。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の一脚の fibration 性での標準比較の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：成分と中央の相対境界が anodyne な重みの制限は一脚の fibration 性で trivial Kan fibration。
方針：境界付きの自然変換を貼り、交換同型による中央の anodyne 性で一脚の相対延長を行う。
規約：図式の中央と右端が Kan、左脚が fibration。重みの相対境界の anodyne 性は入力。
使われ方：Kerodon 7.5.3.12 の重みの制限の全境界の持ち上げ。 -/
lemma weightedSectionsPre_cospan_leftFibration_trivialKanFibration
    {W W' H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    (hk : anodyneExtensions (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)))
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    TrivialKanFibration (weightedSectionsPre j H) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro t s sq
  let P := weightedCorner j (boundary n).ι
  have hw : (j ▷ (Functor.const (AsSmall.{u} WalkingCospan)).obj (boundary n : SSet.{u})) ≫
        weightedSectionsUncurry t =
      (W ◁ (Functor.const (AsSmall.{u} WalkingCospan)).map (boundary n).ι) ≫
        weightedSectionsUncurry s := by
    have h := congrArg weightedSectionsUncurry sq.w
    rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_precomp] at h
    exact h
  let a := P.isPushout.desc (weightedSectionsUncurry t) (weightedSectionsUncurry s) hw
  have h₀ : anodyneExtensions
      (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up P.ι)) :=
    rightCorner_weightedCorner_anodyne j hk (boundary n).ι
  obtain ⟨b, hb⟩ := exists_resized_cospan_extension_of_rightCorner P.ι
    (weightedCorner_obj_anodyne j hj (boundary n).ι (AsSmall.up.obj .left))
    (weightedCorner_obj_anodyne j hj (boundary n).ι (AsSmall.up.obj .right)) h₀ a
  refine CommSq.HasLift.mk' { l := weightedSectionsLift b, fac_left := ?_, fac_right := ?_ }
  · apply (weightedSectionsHomEquiv W' H (boundary n : SSet.{u})).injective
    change weightedSectionsUncurry ((boundary n).ι ≫ weightedSectionsLift b) = _
    rw [weightedSectionsUncurry_precomp, weightedSectionsUncurry_lift]
    calc
      _ = (P.inl ≫ P.ι) ≫ b := congrArg (fun f => f ≫ b) P.inl_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inl_desc _ _ _
  · apply (weightedSectionsHomEquiv W H (Δ[n] : SSet.{u})).injective
    change weightedSectionsUncurry (weightedSectionsLift b ≫ weightedSectionsPre j H) = _
    rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_lift]
    calc
      _ = (P.inr ≫ P.ι) ≫ b := congrArg (fun f => f ≫ b) P.inr_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inr_desc _ _ _

/-- 概要：相対境界が anodyne な重みの制限は一脚の fibration 性でホモトピー同値。
方針：二つの重みの右脚の単射性から両 end の Kan 性を得て、全境界の持ち上げを使う。
規約：重みの単射性と相対境界の anodyne 性を未証明のまま省略しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の一脚の fibration 性での重みの比較。 -/
lemma weightedSectionsPre_cospan_leftFibration_homotopyEquivalence
    {W W' H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    (hk : anodyneExtensions (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)))
    [Mono (W.map (AsSmall.up.map WalkingCospan.Hom.inr))]
    [Mono (W'.map (AsSmall.up.map WalkingCospan.Hom.inr))]
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre j H) := by
  have := weightedSections_cospan_leftFibration_kanComplex W H
  have := weightedSections_cospan_leftFibration_kanComplex W' H
  have := weightedSectionsPre_cospan_leftFibration_trivialKanFibration (H := H) j hj hk
  exact (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
