module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexComposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexDirect
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomPrecompositionLaws

/-!
概要：元の指定分類底変換は標準反復引き戻し同型の元の分類射を介して合成を保つ。
方針：同じ初頂点制限で二つの共役表示を照合し、充満忠実な制限で降下する。
規約：指定底変換と標準比較の分類射を別の同型へ置き換えない。
使われ方：Kerodon §5.6（Tag 027M）、指定Yoneda単位の始点固定正方形の貼り合わせ。
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

local instance straighteningPasting_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

private lemma isoPrecomp_hom {A D X : SSet.{u}} {f g : A ⟶ X}
    (e : FunctorIso f g) (k : D ⟶ A) :
    (e.precomp k).hom = precomposeFunctorHom k e.hom := by
  rw [precomposeFunctorHom_eq_map]
  exact functorIso_precomp_hom e k

private lemma normalized_hom_heq {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (hf : f = f') (hg : g = g') (e : FunctorIso f g) :
    HEq (diagramIsoCongr hf hg e).hom e.hom := by
  subst f' g'
  simpa only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm,
    Iso.refl_trans, Iso.trans_refl] using (HEq.refl e.hom)

/-- 概要：元の二段の指定底変換と標準比較は、同じ始域へ正規化した直接底変換に一致。
方針：同じ初頂点制限の共役表示の等式を、制限の充満忠実性で反映する。
規約：元の同型の等式。使われ方：元の分類射を保ったHomの合成則の回収。 -/
lemma leftStraightening_baseChange_pasting_iso
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory D] [Quasicategory T]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let c := leftClassificationHom q₁ q₀ (pullbackLeftPullbackSndIso p k l).hom
      (pullbackLeftPullbackSndIso_hom_snd p k l)
    letI := leftClassificationHom_preserves_iso q₁ q₀ (pullbackLeftPullbackSndIso p k l)
      (pullbackLeftPullbackSndIso_hom_snd p k l)
      (pullbackLeftPullbackSndIso_inv_snd_snd p k l)
    (leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map l) ≪≫
      leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd p k) l ≪≫ asIso c =
    diagramIsoCongr
      (f' := (SSet.uliftFunctor.{u + 1, u}).map l ≫
        ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningInfinityDiagram p))
      (by rw [Functor.map_comp, Category.assoc]) rfl
      (leftStraighteningInfinityDiagram_baseChangeIso p (l ≫ k)) := by
  dsimp only
  apply functorIso_precomp_injective
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T))
    (localization_pre_isFullyFaithful
      (Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} T)
      SpaceInfinity.{u})
  have hL := leftStraightening_baseChange_composite_simplex p k l
  have hR := leftStraightening_baseChange_direct_simplex p k l
  dsimp only at hL hR
  exact eq_of_heq ((diagramIsoCongr_heq _ _ _).symm.trans
    ((hL.trans hR.symm).heq.trans (diagramIsoCongr_heq _ _ _)))

/-- 概要：元の指定分類底変換の合成は標準反復引き戻し同型の元の分類射と両立。
方針：同じ同型の貼り合わせの等式のHomを取り、始域正規化だけを除く。
規約：元のHomの異種等式で、全図式の射を比較する。
使われ方：指定Yoneda単位の始点固定の照合。対応：Kerodon §5.6（Tag 027M）。 -/
lemma leftStraightening_baseChange_pasting
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory D] [Quasicategory T]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    HEq (precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map l)
        (leftStraighteningInfinityDiagram_baseChangeIso p k).hom ≫
      (leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd p k) l).hom ≫
      leftClassificationHom (pullback.snd (pullback.snd p k) l)
        (pullback.snd p (l ≫ k)) (pullbackLeftPullbackSndIso p k l).hom
        (pullbackLeftPullbackSndIso_hom_snd p k l))
      (leftStraighteningInfinityDiagram_baseChangeIso p (l ≫ k)).hom := by
  have hi := leftStraightening_baseChange_pasting_iso p k l
  dsimp only at hi
  have h := congrArg Iso.hom hi
  simp only [Iso.trans_hom, isoPrecomp_hom, asIso_hom] at h
  exact h.heq.trans (normalized_hom_heq _ _ _)

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
