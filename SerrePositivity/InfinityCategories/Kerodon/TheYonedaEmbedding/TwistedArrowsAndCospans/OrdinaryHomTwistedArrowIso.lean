module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.NerveProductSwapIso

/-!
概要：通常の Hom と twisted arrow の模型比較を、底を含む指定された射の同型にする。
方針：既存の積の nerve の同型・組紐・反対 nerve の同型で底を揃える。
規約：順射は両端の保持を検証した同じ比較射である。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の全 Hom 分類図式の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable (C : Type u) [SmallCategory C]

/-- 元の通常の Hom の底を実際の twisted arrow の底へ移す指定同型。
Kerodon Proposition 8.1.1.10（Tag 03JN）、積と反対の既存の模型移送。 -/
def ordinaryHomBaseIso : nerve (Cᵒᵖ × C) ≅ (nerve C).op ⊗ nerve C :=
  nerveProductSwapIso Cᵒᵖ C ≪≫ (β_ (nerve C) (nerve Cᵒᵖ)) ≪≫
    tensorIso (nerveOppositeIso (C := C)).symm (Iso.refl (nerve C))

/-- 底の指定同型の第一射影は元の反対の源射影である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、底の模型移送の第一成分の法則。 -/
lemma ordinaryHomBaseIso_fst :
    (ordinaryHomBaseIso C).hom ≫ fst (nerve C).op (nerve C) =
      nerveMap (CategoryTheory.Prod.fst Cᵒᵖ C) ≫ (nerveOppositeIso (C := C)).inv := rfl

/-- 底の指定同型の第二射影は元の標的射影である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、底の模型移送の第二成分の法則。 -/
lemma ordinaryHomBaseIso_snd :
    (ordinaryHomBaseIso C).hom ≫ snd (nerve C).op (nerve C) =
      nerveMap (CategoryTheory.Prod.snd Cᵒᵖ C) := rfl

/-- 元の Hom の射影と実際の twisted arrow の射影は底を含む同じ可換四角形を持つ。
Kerodon Proposition 8.1.1.10（Tag 03JN）、全分類図式へ渡す指定射の法則。 -/
lemma ordinaryHomTwistedIso_projection :
    (ordinaryHomTwistedIso C).hom ≫ twistedArrowProjection (nerve C) =
      nerveMap (ordinaryHomElementsProjection C) ≫ (ordinaryHomBaseIso C).hom := by
  letI : IsIso (nerveOppositeMap (C := C)) :=
    (show IsIso (nerveOppositeIso (C := C)).hom from inferInstance)
  change ordinaryHomTwistedComparison C ≫ twistedArrowProjection (nerve C) = _
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, twistedArrowProjection_fst, ordinaryHomBaseIso_fst]
    apply (cancel_mono (nerveOppositeMap (C := C))).mp
    simp only [Category.assoc]
    rw [ordinaryHomTwistedComparison_left]
    have hc : (nerveOppositeIso (C := C)).inv ≫ nerveOppositeMap = 𝟙 (nerve Cᵒᵖ) :=
      (nerveOppositeIso (C := C)).inv_hom_id
    simp only [hc, Category.comp_id]
    rfl
  · simp only [Category.assoc, twistedArrowProjection_snd, ordinaryHomBaseIso_snd]
    rw [ordinaryHomTwistedComparison_right]
    rfl

/-- 同じ全 Hom の模型比較を底も含めた射の圏の指定同型にする。
Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の共同分類図式の比較への入力。 -/
def ordinaryHomTwistedArrowIso :
    Arrow.mk (nerveMap (ordinaryHomElementsProjection C)) ≅
      Arrow.mk (twistedArrowProjection (nerve C)) :=
  Arrow.isoMk (ordinaryHomTwistedIso C) (ordinaryHomBaseIso C)
    (ordinaryHomTwistedIso_projection C)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
