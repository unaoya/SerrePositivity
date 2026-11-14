module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexWhisker
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationPullbackSimplexIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCoefficientComposition

/-!
概要：二段の指定底変換と標準比較の制限の三因子の積を、同じ係数の共役へまとめる。
方針：元の三つの制限同型の表示の中間同型を相殺する。
規約：元の指定同型・元の標準比較の分類を保つ。
使われ方：Kerodon §5.6（Tag 027M）の指定底変換の合成則の降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance simplexComposite_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

private lemma conjugation_chain {L : Type v} [Category.{w} L]
    {a₀ a₁ a₂ a₃ s₀ s₁ s₂ s₃ : L}
    (r₀ : a₀ ≅ s₀) (r₁ : a₁ ≅ s₁) (r₂ : a₂ ≅ s₂) (r₃ : a₃ ≅ s₃)
    (d₀ : s₁ ≅ s₀) (d₁ : s₂ ≅ s₁) (γ : s₃ ≅ s₂) :
    (r₀ ≪≫ d₀.symm ≪≫ r₁.symm) ≪≫
        (r₁ ≪≫ d₁.symm ≪≫ r₂.symm) ≪≫
        (r₂ ≪≫ γ.symm ≪≫ r₃.symm) =
      r₀ ≪≫ (γ ≪≫ d₁ ≪≫ d₀).symm ≪≫ r₃.symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- 概要：二段の元の指定底変換と標準比較の分類の制限は同じ係数の積の共役。
方針：三つの元の制限同型を同じ端点へ移し、中間の制限同型と逆同型を相殺する。
規約：元の分類射の像をasIsoで読むだけ。使われ方：直接底変換との同じ初頂点制限の比較。 -/
lemma leftStraightening_baseChange_composite_simplex
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory D] [Quasicategory T]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor l))
    let s := U.map (nerveMap (transportSimplexFunctor k))
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let c := leftClassificationHom q₁ q₀ (pullbackLeftPullbackSndIso p k l).hom
      (pullbackLeftPullbackSndIso_hom_snd p k l)
    letI := leftClassificationHom_preserves_iso q₁ q₀ (pullbackLeftPullbackSndIso p k l)
      (pullbackLeftPullbackSndIso_hom_snd p k l)
      (pullbackLeftPullbackSndIso_inv_snd_snd p k l)
    diagramIsoCongr
      (by
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality l,
          Category.assoc]
        apply congrArg (fun z ↦ t ≫ z)
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc])
      rfl
      (FunctorIso.precomp
        ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp (U.map l) ≪≫
          leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd p k) l ≪≫ asIso c)
        (U.map (transportSimplexFirstVertexMap T))) =
      ((leftClassificationSimplexIso p).precomp s).precomp t ≪≫
        (simplexSectionCompositeCoefficient p k l ≪≫
          simplexSectionBaseChangeCoefficient (pullback.snd p k) l ≪≫
          (simplexSectionBaseChangeCoefficient p k).precomp t).symm ≪≫
        (leftClassificationSimplexIso q₀).symm := by
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor l))
  have hm : U.map (transportSimplexFirstVertexMap T) ≫
        (U.map l ≫ leftStraighteningInfinityDiagram (pullback.snd p k)) =
      t ≫ (U.map (transportSimplexFirstVertexMap D) ≫
        leftStraighteningInfinityDiagram (pullback.snd p k)) := by
    rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality l, Category.assoc]
  rw [functorIso_precomp_trans, functorIso_precomp_trans,
    diagramIsoCongr_trans_three _ hm rfl _]
  rw [leftStraightening_baseChange_simplex_whisker,
    leftStraightening_baseChange_simplex_normalized]
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  rw [leftClassification_pullbackComparison_simplexIso]
  exact conjugation_chain _ _ _ _ _ _ _

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
