module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletonDiagramSubfunctor
public import SerrePositivity.KST.Spectra.BousfieldKanWeightLatching

/-!
概要：標準単体の有限骨格の重みは Reedy cofibrant。
方針：latching 図式の全ての射は単射なので、各単体次数で骨格の部分図式の余極限も単射。
規約：部分複体骨格の余極限保存は仮定せず、実際の latching 射の包含を比較する。
使われ方：Goerss–Jardine VIII §1。通常 Tot の有限骨格の各段の Kan 性。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.SkeletalStandardLatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 標準単体の関手は単射を単射へ送る。 -/
lemma standard_map_mono {a b : SimplexCategory} (f : a ⟶ b) [Mono f] :
    Mono (stdSimplex.{u}.map f) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro k
  apply (mono_iff_injective _).mpr
  intro x y h
  apply stdSimplex.objEquiv.injective
  apply (cancel_mono f).mp
  exact congrArg stdSimplex.objEquiv h

/-- 標準単体の latching 図式の射は全て単射。 -/
lemma diagram_map_mono (j : SimplexCategory) {a b : LatchingIndex simplex j} (f : a ⟶ b) :
    Mono ((latchingSource simplex j ⋙ stdSimplex.{u}).map f) := by
  let : Mono a.obj.hom := a.property.1
  have : Mono (f.hom.left ≫ b.obj.hom) := by
    rw [Over.w]
    infer_instance
  let : Mono f.hom.left := mono_of_mono f.hom.left b.obj.hom
  change Mono (stdSimplex.map f.hom.left)
  exact standard_map_mono f.hom.left

/-- 有限骨格の標準単体の各 latching 射は単射。 -/
lemma mono (n : ℕ) (j : SimplexCategory) :
    Mono ((latchingComparison simplex j).app
      (stdSimplex.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor n)) := by
  suffices ∀ k, Mono (((latchingComparison simplex j).app
      (stdSimplex.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor n)).app k) from
    NatTrans.mono_of_mono_app _
  intro k
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj k
  let σ : (stdSimplex.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor n) ⋙ E ⟶ stdSimplex.{u} ⋙ E :=
    Functor.whiskerRight
    (Functor.whiskerLeft stdSimplex.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.inclusion n)) E
  let : Mono ((latchingEvaluation simplex j).map σ) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.colimit_mono (latchingSource simplex j ⋙ stdSimplex.{u}) n k
      (fun f ↦ diagram_map_mono j f)
  let : Mono ((latchingComparison simplex j).app stdSimplex.{u}) :=
    StandardSimplexLatching.mono j
  let : Mono ((latchingComparison simplex j).app (stdSimplex.{u} ⋙ E)) :=
    ((MorphismProperty.monomorphisms (Type u)).arrow_iso_iff
      (BousfieldKanWeightLatching.evaluationArrowIso stdSimplex.{u} k j)).mpr
        (inferInstanceAs (Mono (((latchingComparison simplex j).app stdSimplex.{u}).app k)))
  have hc : Mono (((latchingComparison simplex j).app
      ((stdSimplex.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor n) ⋙ E)) ≫ σ.app j) := by
    erw [← (latchingComparison simplex j).naturality σ]
    infer_instance
  have hm := mono_of_mono ((latchingComparison simplex j).app
    ((stdSimplex.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor n) ⋙ E)) (σ.app j)
  exact ((MorphismProperty.monomorphisms (Type u)).arrow_iso_iff
    (BousfieldKanWeightLatching.evaluationArrowIso
      (stdSimplex.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor n) k j)).mp hm

/-- 標準単体の有限骨格の重みは実際の Reedy cofibrant な図式。 -/
lemma reedyCofibrant (n : ℕ) :
    reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u})
      (initial.to (stdSimplex.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor n)) := by
  intro j
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
    (BousfieldKanWeightLatching.initialArrowIso _ j)).mp (mono n j)

end
end SerrePositivity.KST.Spectra.SkeletalStandardLatching
