module

public import SerrePositivity.EInfinity.Hammock.FreeHammockEnrichedPartsData

/-!
# 元の二つの部分と生成矢の像の指定の回収

概要：生成矢の指定を二つの関手へ拡張して戻すと元の指定を回収する。
方針：元の生成矢の回収と対象等式による Hom の移送を使う。
規約：全対象表示の等式を保持する。
使われ方：自由積の二つの元の部分の豊穣関手の普遍性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D]

lemma EnrichedFoldData.parts_foldData (F : EnrichedFoldData W D) : F.parts.foldData = F := by
  let := Hammock.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  let := DiscreteEnrichment.enrichedCategory
    (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
  apply EnrichedFoldData.ext (F := F.parts.foldData) (G := F) rfl
  · rfl
  · apply heq_of_eq
    funext g
    change DiscreteEnrichment.point (unmarkedGeneratorPath W g) ≫
      F.unmarkedEnrichedFunctor.map g.val.left g.val.right ≫ 𝟙 _ = F.generator g
    rw [Category.comp_id]
    exact F.unmarkedEnrichedFunctor_generator g

lemma EnrichedParts.foldData_prefunctor (G : EnrichedParts W D) :
    letI := Hammock.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
    letI := DiscreteEnrichment.enrichedCategory
      (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
    G.foldData.unmarkedPrefunctor = FreeDiscreteEnrichment.functorEquiv G.unmarked := by
  let := Hammock.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  let := DiscreteEnrichment.enrichedCategory
    (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
  apply Prefunctor.ext (F := G.foldData.unmarkedPrefunctor)
    (G := FreeDiscreteEnrichment.functorEquiv G.unmarked)
    (fun X => congrArg (ForgetEnrichment.of SSet.{u}) (G.objects X))
  intro X Y f
  apply eq_of_heq
  simp only [heq_eqRec_iff]
  exact EnrichedHomTransport.point_homOf_heq (G.objects X).symm (G.objects Y).symm
    (DiscreteEnrichment.point f.toPath ≫ G.unmarked.map X Y)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
