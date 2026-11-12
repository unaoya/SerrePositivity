module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.PointJoinCorner

/-!
概要：始対象の付加と可換な nerve の相対境界の anodyne 性。
方針：点との join の自然な同型で標準の相対錐の境界へ移す。
規約：元の nerve の写像が単射かつ anodyne であることを仮定する。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の元の重みから補助重みへの一脚の相対境界。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：元の nerve と始対象を付加した nerve の自然な正方形の相対境界。
方針：通常の包含と WithInitial への関手の拡張の nerve を pushout 上で貼る。
規約：元の関手に忠実性などは要求せず、射だけを定義する。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の元の重み側の比較。 -/
noncomputable def initialNerveCorner (G : C ⥤ D) :
    pushout (nerveMap G) (nerveMap (WithInitial.incl : C ⥤ WithInitial C)) ⟶
      nerve (WithInitial D) :=
  pushout.desc (nerveMap (WithInitial.incl : D ⥤ WithInitial D))
    (nerveMap (WithInitial.map G)) (by rfl)

/-- 概要：元の nerve の写像が単射で anodyne なら始対象を付加した相対境界も anodyne。
方針：自然な点の join の同型で pushout と標的を移し、相対錐の定理を適用する。
規約：元の関手の nerve の単射性と anodyne 性だけを入力とする。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の一脚だけが fibration の cospan の重みの比較。 -/
lemma initialNerveCorner_anodyne (G : C ⥤ D) [Mono (nerveMap G)]
    (hG : anodyneExtensions (nerveMap G)) : anodyneExtensions (initialNerveCorner G) := by
  let eC := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso C
  let eD := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso D
  let f := nerveMap G
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve C)
  have hi : g ≫ eC.hom = nerveMap (WithInitial.incl : C ⥤ WithInitial C) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_initialJoinNerveMap C
  have hs : IsPushout f (nerveMap (WithInitial.incl : C ⥤ WithInitial C))
      (pushout.inl f g) (eC.inv ≫ pushout.inr f g) := by
    apply (IsPushout.of_hasPushout f g).of_iso' (Iso.refl _) (Iso.refl _) eC.symm
      (Iso.refl _)
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
      rw [← hi, Category.assoc, eC.hom_inv_id, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
  have he : initialNerveCorner G = hs.isoPushout.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pointJoinCorner f ≫ eD.hom := by
    apply pushout.hom_ext
    · rw [initialNerveCorner, pushout.inl_desc, ← Category.assoc, ← Category.assoc,
        hs.inl_isoPushout_inv]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pointJoinCorner, pushout.inl_desc]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_initialJoinNerveMap D).symm
    · rw [initialNerveCorner, pushout.inr_desc, ← Category.assoc, ← Category.assoc,
        hs.inr_isoPushout_inv]
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pointJoinCorner, pushout.inr_desc_assoc]
      change nerveMap (WithInitial.map G) =
        eC.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap D
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap_naturality, ← Category.assoc]
      change _ = (eC.inv ≫ eC.hom) ≫ _
      rw [eC.inv_hom_id, Category.id_comp]
  rw [he]
  apply anodyneExtensions.comp_mem _ _ (MorphismProperty.of_isIso _ _)
  exact anodyneExtensions.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pointJoinCorner_anodyne f hG)
    (MorphismProperty.of_isIso _ _)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
