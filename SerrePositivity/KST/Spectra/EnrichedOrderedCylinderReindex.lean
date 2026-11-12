module

public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderNerve

/-!
概要：順序付き円柱の段の選び直しと、標準単体の制限の厳密な可換性。
方針：Hom の順序の証明を単調写像で送り、元の Hom パラメータを保持する。
規約：任意の単調写像で成立。使われ方：零評価の三角形の各辺の照合。
-/

@[expose] public section
noncomputable section
universe u v w w'
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
section
variable {J : Type w} {K : Type w'} [Preorder J] [Preorder K]
  {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 段を単調写像で選び直し、元の Hom を保つ豊穣関手。 -/
def reindex (f : J →o K) : EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object K C) where
  obj X := ⟨f X.position, X.val⟩
  map X Y := {
    app _ := ↾fun ⟨p, a⟩ ↦ (⟨⟨f.monotone p.down.down⟩⟩, a)
    naturality := by intros; rfl }
  map_id X := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    rfl
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨p, a⟩, ⟨q, b⟩⟩
    rfl

/-- 段の包含の選び直しは、像の段への包含。 -/
lemma stageInclusion_reindex (f : J →o K) (i : J) :
    EnrichedFunctor.comp SSet (stageInclusion (C := C) i) (reindex f) = stageInclusion (f i) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

end
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 標準単体の制限と、順序付き円柱の段の選び直しは厳密に可換する。 -/
lemma nerveSimplexFamily_naturality {n m : ℕ} (α : ⦋n⦌ ⟶ ⦋m⦌) :
    (𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.map α) ≫ nerveSimplexFamily m =
      nerveSimplexFamily n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (reindex α.toOrderHom) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨F, t⟩
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  apply SSet.hom_ext
  intro e
  apply ConcreteCategory.hom_ext
  intro P
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

end SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
