module

public import SerrePositivity.InfinityCategories.F2.Presentable.SolutionHomRetraction
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeUniverseContinuity
public import SerrePositivity.InfinityCategories.F2.Presentable.IndLiftedContinuousKan
public import SerrePositivity.InfinityCategories.F2.Presentable.CanonicalKanRetraction
public import SerrePositivity.InfinityCategories.F2.Presentable.CovariantRepresentableRetract
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallLimitsIdempotentComplete
public import SerrePositivity.InfinityCategories.F2.Presentable.IndAccessible

/-!
概要：小極限を持つ Ind 圏上の accessible な極限保存関手を余表現する。
方針：生成解錐の全自然な retract を標準左 Kan 条件で全域へ延長し、元の圏で分裂する。
規約：元の宇宙の filtered 保存と小極限保存だけを要求する。
使われ方：一般の accessible 圏への同値移送による随伴関手定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open Ind

/-- 概要：小極限を持つ Ind 圏の元の κ-連続な極限保存関手は元の対象で余表現可能。
方針：同じ生成解からの Hom retract を全域へ延長し、coherent な冪等分裂を回収する。
規約：小さい空間値の元の関手と指定宇宙変更を全自然に比較する。
使われ方：一般の accessible な極限保存関手の余表現可能性。 -/
lemma ind_corepresentable_of_continuous_preservesLimits
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (A : SSet.{u}) [Quasicategory A]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits (IndInfinity κ A)) (F : IndInfinity κ A ⟶ SpaceInfinity.{u})
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F) (hFl : PreservesSmallLimits F) :
    ∃ x : (IndInfinity κ A) _⦋0⦌,
      Nonempty (FunctorIso (covariantRepresentableInfinity x)
        ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram)) := by
  let j := indYoneda κ A
  obtain ⟨a, d, hd⟩ := exists_generatorSolutionCone
    (indYoneda_isKappaCompactGenerating κ A) F hC hF hFl
  let y := j.app (Opposite.op ⦋0⦌) (ULift.up a)
  let H := (SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram
  let R := covariantRepresentableInfinity y
  let δ := (SSet.uliftFunctor.{u + 2, u + 1}).map j
  have hr := solutionHom_isRetract j F d
  rw [hd] at hr
  have heq : δ ≫ H =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (j ≫ F) ≫ Compact.spaceUniverseDiagram := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (functorVertex (δ ≫ H))
      (functorVertex (δ ≫ R)) := by
    rw [heq]
    exact hr.some
  have hR : Compact.PreservesKappaFilteredColimits.{u, u + 1} κ R :=
    Compact.indYoneda_isKappaCompact κ a
  let r₀ := leftCanonicalRestrictionRetraction δ H R
    (indLiftedContinuous_canonicalColimits κ H hF.spaceUniverse)
    (indLiftedContinuous_canonicalColimits κ R hR) r
  exact covariantRepresentable_retract_corepresentable hC.isIdempotentComplete H y r₀

end SerrePositivity.InfinityCategories.F2.Presentable
