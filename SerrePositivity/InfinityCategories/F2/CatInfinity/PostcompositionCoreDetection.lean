module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorCoreVertexIso
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence
/-!
概要：全試験関手 core の後合成同値性は、元の射の圏同値性を検出する。
方針：標的を試験して右逆を取り、始域の試験の充満忠実性で左逆を回収する。
規約：元の射を保持する。使われ方：実 lax pullback の cospan 輸送の同値判定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.F2
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

lemma isQCatEquivalence_of_postcomposition_core {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (f : A ⟶ B)
    (h : ∀ K : SSet.{u}, IsQCatEquivalence (quasicategoryCoreMap ((ihom K).map f))) :
    IsQCatEquivalence f := by
  obtain ⟨v, ⟨hv⟩⟩ := (h B).choose.isEssentiallySurjective (functorCoreVertex (𝟙 B))
  obtain ⟨g, hg⟩ := (functorVertexEquiv B A).surjective v.val
  have he : FunctorIso (g ≫ f) (𝟙 B) := by
    have e := hv.map (quasicategoryCore ((ihom B).obj B)).ι
    change VertexIso (((ihom B).map f).app _ v.val) (functorVertex (𝟙 B)) at e
    rw [← hg] at e
    exact e
  have hc : FunctorIso ((f ≫ g) ≫ f) ((𝟙 A) ≫ f) := by
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using he.precomp f
  have hc' : VertexIso
      ((quasicategoryCoreMap ((ihom A).map f)).app _ (functorCoreVertex (f ≫ g)))
      ((quasicategoryCoreMap ((ihom A).map f)).app _ (functorCoreVertex (𝟙 A))) :=
    functorIsoCoreVertexIso hc
  have hi := (h A).isFullyFaithful.preimageVertexIso
    (x := functorCoreVertex (f ≫ g)) (y := functorCoreVertex (𝟙 A)) hc'
  have hi' : FunctorIso (f ≫ g) (𝟙 A) :=
    hi.map (quasicategoryCore ((ihom A).obj A)).ι
  exact ⟨g, ⟨hi'⟩, ⟨he⟩⟩

end SerrePositivity.InfinityCategories.F2
