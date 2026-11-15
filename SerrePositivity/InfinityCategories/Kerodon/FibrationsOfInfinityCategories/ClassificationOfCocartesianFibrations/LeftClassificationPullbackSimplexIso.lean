module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexPastingInputs
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionBaseChangeCompClassifiedHom
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomPrecompositionLaws
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：標準反復引き戻し同型の分類を制限すると、同じ補正係数の逆の共役になる。
方針：元の逆射の分類の自然性に同じ順方向の分類を合成して相殺する。
規約：標準同型の元の順方向の射を保持する。
使われ方：Kerodon §5.6（Tag 027M）の指定底変換の三因子の相殺。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Project.QuasicategoryAuxiliaries
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance pullbackSimplexIso_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

private lemma isoPrecomp_hom {A D X : SSet.{u}} {f g : A ⟶ X}
    (e : FunctorIso f g) (k : D ⟶ A) :
    (e.precomp k).hom = precomposeFunctorHom k e.hom := by
  rw [precomposeFunctorHom_eq_map]
  exact functorIso_precomp_hom e k

private lemma precomp_identity {A D X : SSet.{u}} (k : D ⟶ A) (f : A ⟶ X) :
    precomposeFunctorHom k (𝟙 (HomotopyCategory.mk (functorVertex f))) = 𝟙 _ := by
  rw [precomposeFunctorHom_eq_map]
  exact (hoFunctor.map ((pre k).app X)).toFunctor.map_id _

/-- 概要：元の標準反復引き戻し同型の分類の初頂点制限は同じ補正係数の逆の共役。
方針：同じ逆射の分類の自然性と順・逆射の相殺を使う。
規約：元の順方向の分類を保つ。使われ方：指定底変換の合成則の補正因子の相殺。 -/
lemma leftClassification_pullbackComparison_simplexIso {E B D T : SSet.{u}}
    [Quasicategory T] (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let c := leftClassificationHom q₁ q₀ (pullbackLeftPullbackSndIso p k l).hom
      (pullbackLeftPullbackSndIso_hom_snd p k l)
    letI := leftClassificationHom_preserves_iso q₁ q₀ (pullbackLeftPullbackSndIso p k l)
      (pullbackLeftPullbackSndIso_hom_snd p k l)
      (pullbackLeftPullbackSndIso_inv_snd_snd p k l)
    FunctorIso.precomp (asIso c)
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T)) =
      leftClassificationSimplexIso q₁ ≪≫ (simplexSectionCompositeCoefficient p k l).symm ≪≫
        (leftClassificationSimplexIso q₀).symm := by
  dsimp only
  let q₀ := pullback.snd p (l ≫ k)
  let q₁ := pullback.snd (pullback.snd p k) l
  let e := pullbackLeftPullbackSndIso p k l
  let c := leftClassificationHom q₁ q₀ e.hom (pullbackLeftPullbackSndIso_hom_snd p k l)
  let c' := leftClassificationHom q₀ q₁ e.inv (pullbackLeftPullbackSndIso_inv_snd_snd p k l)
  let f := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T)
  letI := leftClassificationHom_preserves_iso q₁ q₀ e
    (pullbackLeftPullbackSndIso_hom_snd p k l) (pullbackLeftPullbackSndIso_inv_snd_snd p k l)
  have hc := congrArg (precomposeFunctorHom f)
    (leftClassificationHom_iso_hom_inv q₁ q₀ e
      (pullbackLeftPullbackSndIso_hom_snd p k l) (pullbackLeftPullbackSndIso_inv_snd_snd p k l))
  rw [precomposeFunctorHom_comp] at hc
  have hcc : precomposeFunctorHom f c ≫ precomposeFunctorHom f c' = 𝟙 _ := by
    exact hc.trans (precomp_identity f (leftStraighteningInfinityDiagram q₁))
  have hn := sectionBaseChangeCompComparison_classified_hom p k l
  change precomposeFunctorHom f c' ≫ (leftClassificationSimplexIso q₁).hom =
    (leftClassificationSimplexIso q₀).hom ≫ (simplexSectionCompositeCoefficient p k l).hom at hn
  have hlo : precomposeFunctorHom f c ≫
      ((leftClassificationSimplexIso q₀).hom ≫ (simplexSectionCompositeCoefficient p k l).hom) =
      (leftClassificationSimplexIso q₁).hom := by
    rw [← hn, ← Category.assoc, hcc, Category.id_comp]
  have heq : (FunctorIso.precomp (asIso c) f).hom ≫
      ((leftClassificationSimplexIso q₀).hom ≫ (simplexSectionCompositeCoefficient p k l).hom) =
      (leftClassificationSimplexIso q₁).hom := by
    rw [isoPrecomp_hom, asIso_hom]
    exact hlo
  change FunctorIso.precomp (asIso c) f =
    leftClassificationSimplexIso q₁ ≪≫ (simplexSectionCompositeCoefficient p k l).symm ≪≫
      (leftClassificationSimplexIso q₀).symm
  apply Iso.ext
  apply (cancel_mono
    ((leftClassificationSimplexIso q₀).hom ≫ (simplexSectionCompositeCoefficient p k l).hom)).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using heq

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
