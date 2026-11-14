module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NormalizedFunctorIsoComponentRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoTransposeValue

/-!
概要：指定初頂点制限同型の一対象成分を、同じ共同制限同型の係数評価へ戻す。
方針：転置・成分・端点正規化の既存の法則を同じ比較へ適用する。
規約：元の制限同型を保持する。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の貼り合わせの中間因子の消去。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.LimitsAndColimits.LimitsAndColimits
open Project.LocalizationAndKanExtensionAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

private lemma mp_heq {α β : Sort v} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
  cases h
  rfl

private lemma iso_trans_eqToIso_heq {L : Type v} [Category.{w} L]
    {a b c : L} (e : a ≅ b) (h : b = c) : HEq (e ≪≫ eqToIso h) e := by
  cases h
  simpa only [eqToIso_refl, Iso.trans_refl] using (HEq.refl e)

/-- 概要：初頂点制限の指定全対象同型は、同じ共同制限同型の転置と端点移送だけ異なる。
方針：元の定義の一回の型移送と、二重転置の終点移送を消去する。
規約：同じ同型の異種等式。使われ方：元の係数評価へ制限同型を戻す。 -/
lemma leftStraighteningSimplexRestrictionIso_heq_transpose (B : SSet.{u}) :
    HEq (leftStraighteningSimplexRestrictionIso B)
      (leftStraighteningSectionJointDiagram_restrictIso B).transpose := by
  have h₀ : HEq (leftStraighteningSimplexRestrictionIso B)
      (leftStraighteningInfinityMap_restrictIso B) := by
    exact iso_trans_eqToIso_heq (leftStraighteningInfinityMap_restrictIso B)
      (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f))
        (internalHomFlipHomEquiv_transposeFunctorFamily
          (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization))
  have h₁ : HEq (leftStraighteningInfinityMap_restrictIso B)
      (leftStraighteningSectionJointDiagram_restrictIso B).transpose := by
    unfold leftStraighteningInfinityMap_restrictIso
    dsimp only [_root_.id]
    exact mp_heq _ _
  exact h₀.trans h₁

/-- 概要：指定した初頂点制限の元の対象成分は、同じ共同制限同型の評価後合成。
方針：同じ成分の正規化を消去し、転置の同じ値の法則を使う。
規約：元の同型自身の異種等式。使われ方：指定底変換の中間制限同型の消去。 -/
lemma leftClassificationSimplexIso_heq_joint_postcomp {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    HEq (leftClassificationSimplexIso p)
      ((leftStraighteningSectionJointDiagram_restrictIso B).postcomp
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p))) := by
  have hn := normalizedFunctorIsoComponent_heq_app (leftStraighteningSimplexRestrictionIso B)
    (leftFibrationInfinityVertex p) (leftClassificationSimplex_sourceEq p)
    (leftClassificationSimplex_targetEq p)
  rw [leftClassificationSimplex_component] at hn
  have hnv := hn.trans (functorIsoValue_eq_app (leftStraighteningSimplexRestrictionIso B)
    (leftFibrationInfinityVertex p)).symm.heq
  have hf := transposeFunctorFamily_comp
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))
    (leftStraighteningSectionJointDiagram B)
  have hg : transposeFunctorFamily (transportSimplexSectionInfinity B) =
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization :=
    internalHomFlipHomEquiv_transposeFunctorFamily
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization
  have hv := functorIsoValue_heq_of_heq (leftStraighteningSimplexRestrictionIso B)
    (leftStraighteningSectionJointDiagram_restrictIso B).transpose hf.symm hg.symm
    (leftStraighteningSimplexRestrictionIso_heq_transpose B) (leftFibrationInfinityVertex p)
  exact hnv.trans (hv.trans (functorIsoValue_transpose_heq_postcomp
    (leftStraighteningSectionJointDiagram_restrictIso B) (leftFibrationInfinityVertex p)))

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
