module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.SmallPushout
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.KappaSmallProducts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalEndpointPullback
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

/-!
概要：射の元の全試験族と、追加した始点の余錐を貼り合わせる実補間領域。
方針：元の始点の全族に沿う pushout で、円柱と始点余錐を厳密に接着する。
規約：任意の κ-small 試験形状。使われ方：射の二段 filtered 表示。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の円柱族と新しい始点の余錐を、同じ全始点族で貼った領域。 -/
def arrowInterpolationCorner (A : SSet.{u}) : SSet.{u} :=
  pushout (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u}))

/-- 補間領域の実際の全円柱への比較。 -/
def arrowInterpolationCornerInclusion (A : SSet.{u}) :
    arrowInterpolationCorner A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⊗ Δ[1] :=
  pushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ▷ (Δ[1] : SSet.{u})) SSet.ι₀ (by
    exact SSet.ι₀_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})))

/-- 元の円柱族は、同じ元の全包含で比較される。 -/
lemma arrowInterpolationCornerInclusion_old (A : SSet.{u}) :
    pushout.inl SSet.ι₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})) ≫
      arrowInterpolationCornerInclusion A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ▷ (Δ[1] : SSet.{u}) :=
  pushout.inl_desc _ _ _

/-- 追加した始点余錐は、全円柱の零端点に厳密に一致する。 -/
lemma arrowInterpolationCornerInclusion_source (A : SSet.{u}) :
    pushout.inr SSet.ι₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})) ≫
      arrowInterpolationCornerInclusion A = (SSet.ι₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0] ⊗ Δ[1]) :=
  pushout.inr_desc _ _ _

/-- 二つの元の境界を貼った補間領域は、全円柱の実際の部分図式。 -/
instance arrowInterpolationCornerInclusion_mono (A : SSet.{u}) :
    Mono (arrowInterpolationCornerInclusion A) := by
  haveI : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) :=
    (tensorRight (Δ[1] : SSet.{u})).map_mono _
  let h := IsPushout.of_hasPushout (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0])
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPullback_ι₀_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u}))
  have he : h.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ▷ (Δ[1] : SSet.{u})) SSet.ι₀ hp.w =
      arrowInterpolationCornerInclusion A := by
    apply pushout.hom_ext
    · rw [h.inl_desc, arrowInterpolationCornerInclusion_old]
    · rw [h.inr_desc, arrowInterpolationCornerInclusion_source]
  rw [← he]
  exact h.desc_mono_of_isPullback hp

/-- 正則 κ に対して、この実補間領域も κ-small。 -/
lemma arrowInterpolationCorner_isKappaSmall {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {A : SSet.{u}} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (arrowInterpolationCorner A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isKappaSmall_pushout_of_mono hκ SSet.ι₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_prod hκ hA (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hκ.aleph0_le _))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_join hκ hA (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hκ.aleph0_le _))

/-- 元の円柱族と同じ境界上で一致する始点余錐の全図式を厳密に貼る。 -/
def arrowInterpolationGlue {A X : SSet.{u}} (F : A ⊗ Δ[1] ⟶ X)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X)
    (h : SSet.ι₀ ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ G) : arrowInterpolationCorner A ⟶ X :=
  pushout.desc F G h

/-- 貼り合わせた全図式の元の円柱側の制限は元の全族そのもの。 -/
lemma arrowInterpolationGlue_old {A X : SSet.{u}} (F : A ⊗ Δ[1] ⟶ X)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X) (h) :
    pushout.inl SSet.ι₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) ≫ arrowInterpolationGlue F G h = F :=
  pushout.inl_desc _ _ _

/-- 貼り合わせた全図式の始点余錐への制限も元の全射そのもの。 -/
lemma arrowInterpolationGlue_source {A X : SSet.{u}} (F : A ⊗ Δ[1] ⟶ X)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X) (h) :
    pushout.inr SSet.ι₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) ≫ arrowInterpolationGlue F G h = G :=
  pushout.inr_desc _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
