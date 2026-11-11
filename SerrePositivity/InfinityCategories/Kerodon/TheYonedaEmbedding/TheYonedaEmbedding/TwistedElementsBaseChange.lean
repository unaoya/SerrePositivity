module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange

/-!
概要：終点だけで引き戻した twisted arrow の族を、共同 Hom の底変換として表示する。
方針：二つの引き戻しの射影から互いに逆な射を構成する。
規約：元の底・終点・共同射影を厳密に保持する。
使われ方：密度の大域 pointed 評価を、同じ共同 Hom 図式の自然変換へ移す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {E C : SSet.{u}} (p : E ⟶ C)

/-- 始点と指定された全空間の終点を記録する共同射影。 -/
def twistedElementsProjection : pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) p ⟶ C.op ⊗ E :=
  lift (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C) (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) p)

/-- 終点の構造射で元の共同 Hom の底へ戻す射。 -/
def twistedElementsBaseMap : C.op ⊗ E ⟶ C.op ⊗ C :=
  lift (fst C.op E) (snd C.op E ≫ p)

/-- 同じ共同射影の正方形は厳密に可換。 -/
lemma twistedElementsProjection_base :
    twistedElementsProjection p ≫ twistedElementsBaseMap p =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, twistedElementsBaseMap, twistedElementsProjection,
      lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst]
  · simp only [Category.assoc, twistedElementsBaseMap, twistedElementsProjection,
      lift_snd, lift_snd_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd, pullback.condition]

/-- 終点の引き戻しから、共同 Hom の同じ底変換への比較。 -/
def twistedElementsToBaseChange : pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) p ⟶
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (twistedElementsBaseMap p) :=
  pullback.lift (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) p) (twistedElementsProjection p)
    (twistedElementsProjection_base p).symm

/-- 共同 Hom の底変換から、同じ終点の引き戻しへ戻す比較。 -/
def twistedElementsFromBaseChange :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (twistedElementsBaseMap p) ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ snd C.op E) (by
    have h := congrArg (fun f ↦ f ≫ snd C.op C)
      (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (g := twistedElementsBaseMap p))
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd,
      twistedElementsBaseMap, lift_snd] using h)

/-- 元の終点を保つ全族は、共同 Hom の底変換と厳密に同型。 -/
def twistedElementsBaseChangeIso : pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) p ≅
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (twistedElementsBaseMap p) where
  hom := twistedElementsToBaseChange p
  inv := twistedElementsFromBaseChange p
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [twistedElementsToBaseChange, twistedElementsFromBaseChange,
        Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [twistedElementsToBaseChange, twistedElementsFromBaseChange,
        Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, twistedElementsProjection,
        lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [twistedElementsToBaseChange, twistedElementsFromBaseChange,
        Category.assoc, pullback.lift_fst, Category.id_comp]
    · apply CartesianMonoidalCategory.hom_ext
      · have h := congrArg (fun f ↦ f ≫ fst C.op C)
          (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (g := twistedElementsBaseMap p))
        simpa only [twistedElementsToBaseChange, twistedElementsFromBaseChange,
          twistedElementsProjection, Category.assoc, pullback.lift_snd, pullback.lift_fst,
          pullback.lift_fst_assoc,
          lift_fst, Category.id_comp, twistedElementsBaseMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst] using h
      · simp only [twistedElementsToBaseChange, twistedElementsFromBaseChange,
          twistedElementsProjection, Category.assoc, pullback.lift_snd, lift_snd, Category.id_comp]

/-- 同じ底変換表示は、元の共同射影を厳密に回収する。 -/
lemma twistedElementsBaseChangeIso_projection :
    (twistedElementsBaseChangeIso p).hom ≫ pullback.snd _ _ = twistedElementsProjection p :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
