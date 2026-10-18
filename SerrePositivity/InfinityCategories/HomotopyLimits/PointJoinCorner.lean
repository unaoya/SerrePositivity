module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeConeAnodyne
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：点の相対錐の anodyne 性を pushout の標準境界として表示する。
方針：単射の像と空 join の同型で joinUnion の pushout を移送する。
規約：元の写像は単射で anodyne であると仮定する。
使われ方：Kerodon 7.5.3.12 の一脚だけが fibration の重みの相対境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {A B : SSet.{u}}

/-- 概要：B と点の A 上の錐を A 上で貼り合わせ、点の B 上の錐へ写す相対境界。
方針：右包含の自然性で pushout からの射を作る。
規約：左包含は B、右包含は Δ[0] ⋆ A。
使われ方：Kerodon 7.5.3.12 の元の重みから補助重みへの相対境界。 -/
noncomputable def pointJoinCorner (f : A ⟶ B) :
    pushout f (joinInr (Δ[0] : SSet.{u}) A) ⟶ join (Δ[0] : SSet.{u}) B :=
  pushout.desc (joinInr (Δ[0] : SSet.{u}) B) (joinMap (𝟙 _) f)
    (by rw [joinInr_joinMap])

private lemma pointJoinUnion_pushout (f : A ⟶ B) [Mono f] :
    IsPushout f (joinInr (Δ[0] : SSet.{u}) A)
      (joinInr ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) B ≫
        joinUnionLeft ⊥ (Subcomplex.range f))
      (joinMap (𝟙 (Δ[0] : SSet.{u})) (Subfunctor.toRange f) ≫
        joinUnionRight ⊥ (Subcomplex.range f)) := by
  let R := Subcomplex.range f
  let E : SSet.{u} := (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
  let t := Subfunctor.toRange f
  have : IsIso t := Subfunctor.instIsIsoFunctorTypeToRangeOfMono f
  apply (joinUnion_isPushout (⊥ : (Δ[0] : SSet.{u}).Subcomplex) R).of_iso'
    (asIso t ≪≫ (emptyJoinIso Δ[0] (R : SSet.{u})).symm)
    (emptyJoinIso Δ[0] B).symm (joinIso (Iso.refl (Δ[0] : SSet.{u})) (asIso t))
    (Iso.refl _)
  · change t ≫ joinInr E (R : SSet.{u}) ≫ joinMap (𝟙 E) R.ι = f ≫ joinInr E B
    rw [joinInr_joinMap, ← Category.assoc, Subfunctor.toRange_ι]
  · change t ≫ joinInr E (R : SSet.{u}) ≫ joinMap (⊥ :
      (Δ[0] : SSet.{u}).Subcomplex).ι (𝟙 (R : SSet.{u})) =
        joinInr (Δ[0] : SSet.{u}) A ≫ joinMap (𝟙 _) t
    rw [joinInr_joinMap, joinInr_joinMap, Category.id_comp]
  · rfl
  · rfl

/-- 概要：単射で anodyne な写像の点の相対錐の標準境界は anodyne である。
方針：像に対する joinUnion の相対錐を使い、pushout の同型で移送する。
規約：A と B 自身の Kan 性は要求しない。
使われ方：Kerodon 7.5.3.12 の一脚だけが fibration の cospan の重みの比較。 -/
lemma pointJoinCorner_anodyne (f : A ⟶ B) [Mono f] (hf : anodyneExtensions f) :
    anodyneExtensions (pointJoinCorner f) := by
  let hs := pointJoinUnion_pushout f
  have he : pointJoinCorner f = hs.isoPushout.inv ≫ (joinUnion
      (⊥ : (Δ[0] : SSet.{u}).Subcomplex) (Subcomplex.range f)).ι := by
    apply pushout.hom_ext
    · rw [pointJoinCorner, pushout.inl_desc, ← Category.assoc, hs.inl_isoPushout_inv]
      rw [Category.assoc, joinUnionLeft_ι, joinInr_joinMap, Category.id_comp]
    · rw [pointJoinCorner, pushout.inr_desc, ← Category.assoc, hs.inr_isoPushout_inv]
      rw [Category.assoc, joinUnionRight_ι, ← joinMap_comp, Category.id_comp,
        Subfunctor.toRange_ι]
  rw [he]
  apply anodyneExtensions.comp_mem _ _ (MorphismProperty.of_isIso _ _)
  have hv := joinUnion_pointBoundary_range_anodyne f hf
  rw [SSet.boundary_zero] at hv
  exact hv

end SerrePositivity.InfinityCategories.HomotopyLimits
