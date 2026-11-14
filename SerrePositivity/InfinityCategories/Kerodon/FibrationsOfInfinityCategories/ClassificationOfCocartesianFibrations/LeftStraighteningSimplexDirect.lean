module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCoefficientComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexPastingInputs
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport

/-!
概要：直接の指定底変換の制限を、二段の元の係数の積の同じ共役として読む。
方針：元の係数貼り合わせと単体圏関手の合成則で同じ係数表示を揃える。
規約：直接底変換の元の同型を保持する。
使われ方：Kerodon §5.6（Tag 027M）の初頂点制限での同じ合成式の比較。
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

local instance simplexDirect_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

private lemma isoSymm_heq {L : Type v} [Category.{w} L]
    {a b a' b' : L} (e : a ≅ b) (e' : a' ≅ b')
    (ha : a = a') (hb : b = b') (h : HEq e e') : HEq e.symm e'.symm := by
  subst a' b'
  cases eq_of_heq h
  rfl

private lemma isoThree_heq {L : Type v} [Category.{w} L]
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : L}
    (e₁ : a₀ ≅ a₁) (e₂ : a₁ ≅ a₂) (e₃ : a₂ ≅ a₃)
    (d₁ : b₀ ≅ b₁) (d₂ : b₁ ≅ b₂) (d₃ : b₂ ≅ b₃)
    (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃)
    (he₁ : HEq e₁ d₁) (he₂ : HEq e₂ d₂) (he₃ : HEq e₃ d₃) :
    HEq (e₁ ≪≫ e₂ ≪≫ e₃) (d₁ ≪≫ d₂ ≪≫ d₃) := by
  subst b₀ b₁ b₂ b₃
  cases eq_of_heq he₁
  cases eq_of_heq he₂
  cases eq_of_heq he₃
  rfl

/-- 概要：直接の指定底変換を同じ合成始域へ移して制限すると、二段係数の積の共役。
方針：単体圏の合成と同じ係数貼り合わせを指定共役表示へ適用する。
規約：全図式の元の同型の等式。使われ方：二段指定底変換との照合後の忠実性による降下。 -/
lemma leftStraightening_baseChange_direct_simplex
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory T]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor l))
    let s := U.map (nerveMap (transportSimplexFunctor k))
    diagramIsoCongr
      (by
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality l,
          Category.assoc]
        apply congrArg (fun z ↦ t ≫ z)
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc])
      rfl
      (FunctorIso.precomp
        (diagramIsoCongr
          (f' := U.map l ≫ (U.map k ≫ leftStraighteningInfinityDiagram p))
          (by rw [Functor.map_comp, Category.assoc]) rfl
          (leftStraighteningInfinityDiagram_baseChangeIso p (l ≫ k)))
        (U.map (transportSimplexFirstVertexMap T))) =
      ((leftClassificationSimplexIso p).precomp s).precomp t ≪≫
        (simplexSectionCompositeCoefficient p k l ≪≫
          simplexSectionBaseChangeCoefficient (pullback.snd p k) l ≪≫
          (simplexSectionBaseChangeCoefficient p k).precomp t).symm ≪≫
        (leftClassificationSimplexIso (pullback.snd p (l ≫ k))).symm := by
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor l))
  let s := U.map (nerveMap (transportSimplexFunctor k))
  let r := U.map (nerveMap (transportSimplexFunctor (l ≫ k)))
  let P := simplexSectionCompositeCoefficient p k l ≪≫
    simplexSectionBaseChangeCoefficient (pullback.snd p k) l ≪≫
    (simplexSectionBaseChangeCoefficient p k).precomp t
  have ht : r = t ≫ s := (transportSimplexNerveFunctor ⋙ U).map_comp l k
  have hs : t ≫ (s ≫ (U.map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningInfinityDiagram p)) =
      r ≫ (U.map (transportSimplexFirstVertexMap B) ≫ leftStraighteningInfinityDiagram p) := by
    rw [← Category.assoc, ← ht]
  have hc : t ≫ (s ≫ simplexSectionValue p) = r ≫ simplexSectionValue p := by
    rw [← Category.assoc, ← ht]
  have hr : HEq (((leftClassificationSimplexIso p).precomp s).precomp t)
      ((leftClassificationSimplexIso p).precomp r) :=
    (functorIso_precomp_precomp (leftClassificationSimplexIso p) s t).heq.trans
      (functorIso_precomp_heq_of_map_eq (leftClassificationSimplexIso p) ht).symm
  have hd := isoSymm_heq P (simplexSectionBaseChangeCoefficient p (l ≫ k)) rfl
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) hc)
    (simplexSectionBaseChangeCoefficient_pasting p k l)
  have hp := isoThree_heq
    (((leftClassificationSimplexIso p).precomp s).precomp t) P.symm
    (leftClassificationSimplexIso (pullback.snd p (l ≫ k))).symm
    ((leftClassificationSimplexIso p).precomp r)
    (simplexSectionBaseChangeCoefficient p (l ≫ k)).symm
    (leftClassificationSimplexIso (pullback.snd p (l ≫ k))).symm
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) hs)
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) hc)
    rfl rfl hr hd (HEq.refl _)
  have hg : U.map (l ≫ k) ≫ leftStraighteningInfinityDiagram p =
      U.map l ≫ (U.map k ≫ leftStraighteningInfinityDiagram p) := by
    rw [Functor.map_comp, Category.assoc]
  let b := leftStraighteningInfinityDiagram_baseChangeIso p (l ≫ k)
  let N := diagramIsoCongr hg rfl b
  have hn := functorIso_precomp_heq_of_heq b N hg rfl
    (diagramIsoCongr_heq hg rfl b) (U.map (transportSimplexFirstVertexMap T))
  exact eq_of_heq ((diagramIsoCongr_heq _ _ _).trans
    (hn.trans ((leftStraightening_baseChange_firstVertex_coefficient p (l ≫ k)).trans hp.symm)))

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
