module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CospanRightCorner
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedExtensions
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightMapMono

/-!
概要：一脚が fibration の cospan の重み付き end の Kan 性。
方針：ホーンと重みの直積の中央の相対境界を pushout-product として anodyne にする。
規約：重みの右脚の単射性と、図式の中央と右端の Kan 性・左脚の Fibration 性を明示する。
使われ方：Kerodon 7.5.3.12、7.5.4.1 の一脚だけが fibration の引き戻し。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：単射である重みの右脚と anodyne なパラメーターの相対境界は anodyne。
方針：中央の相対境界を二つの単体集合の射の pushout-product と同定する。
規約：重みの右脚には単射性だけを要求する。
使われ方：Kerodon 7.5.3 の一脚の fibration 性でのホーン充填。 -/
lemma cospanRightCorner_tensor_anodyne (W : WalkingCospan ⥤ SSet.{u})
    [Mono (W.map WalkingCospan.Hom.inr)] {A B : SSet.{u}} (f : A ⟶ B)
    (hf : anodyneExtensions f) :
    anodyneExtensions (cospanRightCornerMap (W ◁ (Functor.const WalkingCospan).map f)) := by
  let P := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    (W.map WalkingCospan.Hom.inr) f
  change anodyneExtensions P.ι
  exact anodyneExtensions_pushoutObjObjι P hf

/-- 概要：係数の宇宙へ持ち上げた重みでも、直積の中央の相対境界は anodyne。
方針：AsSmall.up で制限し、同じ pushout-product の定理を適用する。
規約：境界は reindex した図式の射の cospanRightCornerMap として表示する。
使われ方：Kerodon 7.5.3、任意の宇宙の cospan の end の充填。 -/
lemma resized_cospanRightCorner_tensor_anodyne
    (W : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [Mono (W.map (AsSmall.up.map WalkingCospan.Hom.inr))]
    {A B : SSet.{u}} (f : A ⟶ B) (hf : anodyneExtensions f) :
    anodyneExtensions (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up
      (W ◁ (Functor.const (AsSmall.{u} WalkingCospan)).map f))) := by
  have : Mono ((AsSmall.up ⋙ W).map WalkingCospan.Hom.inr) :=
    inferInstanceAs (Mono (W.map (AsSmall.up.map WalkingCospan.Hom.inr)))
  exact cospanRightCorner_tensor_anodyne (AsSmall.up ⋙ W) f hf

/-- 概要：重みの右脚が単射なら、一脚が fibration の Kan cospan の end は Kan。
方針：ホーンを転置し、中央の相対境界を pushout-product で埋め、右端と左脚で相対延長する。
規約：図式の右脚の Fibration 性は不要。中央と右端の Kan 性は要求する。
使われ方：Kerodon 7.5.3.12、7.5.4.1 の一脚の fibration 性での比較先。 -/
lemma weightedSections_cospan_leftFibration_kanComplex
    (W H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [Mono (W.map (AsSmall.up.map WalkingCospan.Hom.inr))]
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    KanComplex (weightedSections W H) := by
  apply kanComplex_of_rightHornFillers
  intro n i _ σ
  let j := W ◁ (Functor.const (AsSmall.{u} WalkingCospan)).map (horn (n + 1) i).ι
  have hj (k) : anodyneExtensions (j.app k) :=
    (anodyneExtensions.horn_ι i).whiskerLeft (W.obj k)
  have h₀ : anodyneExtensions (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)) :=
    resized_cospanRightCorner_tensor_anodyne W _ (anodyneExtensions.horn_ι i)
  obtain ⟨b, hb⟩ := exists_resized_cospan_extension_of_rightCorner j (hj _) (hj _) h₀
    (weightedSectionsUncurry σ)
  refine ⟨weightedSectionsLift b, ?_⟩
  apply (weightedSectionsHomEquiv W H (horn (n + 1) i : SSet.{u})).injective
  change weightedSectionsUncurry ((horn (n + 1) i).ι ≫ weightedSectionsLift b) = _
  rw [weightedSectionsUncurry_precomp, weightedSectionsUncurry_lift]
  exact hb

/-- 概要：中央と右端が Kan、左脚だけが fibration の cospan の Bousfield–Kan end は Kan。
方針：添字の右脚が単射なので重みの右脚も単射となり、相対的なホーン充填を適用する。
規約：図式の右脚の fibration 性やその代わりの比較仮定は要求しない。
使われ方：Kerodon 7.5.3.12、7.5.4.1 の一脚の fibration 性での homotopy 極限の模型。 -/
lemma bousfieldKanHolim_cospan_leftFibration_kanComplex
    (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    KanComplex (bousfieldKanHolim H) := by
  have : (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_functor
  have := bousfieldKanWeight_map_mono (AsSmall.up.map WalkingCospan.Hom.inr)
  exact weightedSections_cospan_leftFibration_kanComplex _ H

end SerrePositivity.InfinityCategories.HomotopyLimits
