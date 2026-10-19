module

public import SerrePositivity.KST.Spectra.WeightTensorLatching
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：重みの射に右 tensor する操作は実際の相対 latching 射と交換する。
方針：latching の交換同型を重みの射に自然にし、押し出しの保存を合成する。
規約：パラメーターの射ではなく、重みの射の相対 latching を扱う。
使われ方：Goerss–Jardine VII §4。置換単位の相対 pushout-product の計算。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.WeightTensorLatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F G : CosimplicialObject SSet.{u}} (θ : F ⟶ G) (A : SSet.{u}) (j : SimplexCategory)

/-- latching と右 tensor の交換同型は重みの自然変換にも自然。 -/
lemma iso_weight_natural :
    (latchingEvaluation simplex j).map (Functor.whiskerRight θ (tensorRight A)) ≫
        (iso G A j).hom =
      (iso F A j).hom ≫ ((latchingEvaluation simplex j).map θ ▷ A) := by
  change colim.map (Functor.whiskerLeft (latchingSource simplex j)
      (Functor.whiskerRight θ (tensorRight A))) ≫ _ = _ ≫
    (colim.map (Functor.whiskerLeft (latchingSource simplex j) θ) ▷ A)
  apply colimit.hom_ext
  intro k
  rw [← Category.assoc, colimit.ι_map, Category.assoc]
  change (θ.app k.obj.left ▷ A) ≫
    (colimit.ι ((latchingSource simplex j ⋙ G) ⋙ tensorRight A) k ≫
      (preservesColimitIso (tensorRight A) (latchingSource simplex j ⋙ G)).inv) =
    colimit.ι ((latchingSource simplex j ⋙ F) ⋙ tensorRight A) k ≫
      (preservesColimitIso (tensorRight A) (latchingSource simplex j ⋙ F)).inv ≫ _
  rw [ι_preservesColimitIso_inv, ι_preservesColimitIso_inv_assoc]
  change (θ.app k.obj.left ▷ A) ≫ (colimit.ι (latchingSource simplex j ⋙ G) k ▷ A) =
    (colimit.ι (latchingSource simplex j ⋙ F) k ▷ A) ≫
      (colim.map (Functor.whiskerLeft (latchingSource simplex j) θ) ▷ A)
  rw [← comp_whiskerRight, ← comp_whiskerRight, colimit.ι_map]
  rfl

/-- 相対 latching の押し出しを tensor した二辺の押し出しへ送る。 -/
abbrev weightPushoutMap :=
  pushout.map
    ((latchingEvaluation simplex j).map (Functor.whiskerRight θ (tensorRight A)))
    ((latchingComparison simplex j).app (diagram F A))
    ((latchingEvaluation simplex j).map θ ▷ A) ((latchingComparison simplex j).app F ▷ A)
    (iso G A j).hom (𝟙 _) (iso F A j).hom (iso_weight_natural θ A j)
    ((Category.comp_id _).trans (iso_comparison F A j).symm)

instance weightPushoutMap_isIso : IsIso (weightPushoutMap θ A j) :=
  pushout.map_isIso _ _ _ _ (iso G A j).hom (𝟙 _) (iso F A j).hom _ _

/-- 右 tensor は重みの射の相対 latching と標準の arrow 同型で交換する。 -/
def relativeWeightTensorArrowIso :
    Arrow.mk (relativeLatchingMap simplex j (Functor.whiskerRight θ (tensorRight A))) ≅
      Arrow.mk (relativeLatchingMap simplex j θ ▷ A) := by
  let e := asIso (weightPushoutMap θ A j) ≪≫
    PreservesPushout.iso (tensorRight A)
      ((latchingEvaluation simplex j).map θ) ((latchingComparison simplex j).app F)
  refine Arrow.isoMk e (Iso.refl _) ?_
  change (weightPushoutMap θ A j ≫ _) ≫ (relativeLatchingMap simplex j θ ▷ A) = _ ≫ 𝟙 _
  rw [Category.comp_id]
  apply pushout.hom_ext
  · rw [← Category.assoc, ← Category.assoc, pushout.inl_desc, Category.assoc]
    simp only [Category.assoc]
    erw [PreservesPushout.inl_iso_hom_assoc (tensorRight A)
      ((latchingEvaluation simplex j).map θ) ((latchingComparison simplex j).app F)]
    change (iso G A j).hom ≫
      (pushout.inl ((latchingEvaluation simplex j).map θ)
        ((latchingComparison simplex j).app F) ▷ A) ≫
      (relativeLatchingMap simplex j θ ▷ A) = _
    rw [← comp_whiskerRight, inl_relativeLatchingMap, iso_comparison]
    exact (inl_relativeLatchingMap simplex j (Functor.whiskerRight θ (tensorRight A))).symm
  · rw [← Category.assoc, ← Category.assoc, pushout.inr_desc, Category.id_comp]
    erw [PreservesPushout.inr_iso_hom (tensorRight A)
      ((latchingEvaluation simplex j).map θ) ((latchingComparison simplex j).app F)]
    change (pushout.inr ((latchingEvaluation simplex j).map θ)
      ((latchingComparison simplex j).app F) ▷ A) ≫
      (relativeLatchingMap simplex j θ ▷ A) = _
    rw [← comp_whiskerRight, inr_relativeLatchingMap]
    exact (inr_relativeLatchingMap simplex j (Functor.whiskerRight θ (tensorRight A))).symm

/-- Reedy anodyne な重みの射は右 tensor の後でも Reedy anodyne。 -/
lemma whiskerRight_reedy_anodyne (hθ : reedyLeft simplex anodyneExtensions θ) :
    reedyLeft simplex anodyneExtensions (Functor.whiskerRight θ (tensorRight A)) := by
  intro j
  exact (anodyneExtensions.arrow_iso_iff (relativeWeightTensorArrowIso θ A j)).mpr
    ((hθ j).whiskerRight A)

end
end SerrePositivity.KST.Spectra.WeightTensorLatching
