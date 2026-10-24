module

public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulHomComparison
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafSubcategory
public import SerrePositivity.InfinityCategories.F2.Compact.YonedaEvaluationClassification

/-!
概要：Ind の元の Yoneda 対象からの全 Hom を前層評価の小さい模型と比較する。
方針：全部分包含の全 Hom 比較と元の前層 Yoneda 評価比較を合成する。
規約：元の Yoneda 対象と元の評価関手を保持する。
使われ方：右随伴の accessibility を小さい評価族で検査する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の Ind Yoneda からの全共変 Hom は元の前層評価の宇宙変更と全自然同型。
方針：同じ対象を前層包含で写し、Yoneda 評価の全自然比較を制限する。
規約：κ の正則性や追加の交換定理を要求しない。
使われ方：右随伴の元の小さい filtered 余極限保存の評価判定。 -/
def indYonedaHom_evaluationIso (κ : Cardinal.{u}) (A : SSet.{u}) [Quasicategory A]
    (a : A _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity
      ((Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map
        (Ind.indInclusionPresheaf κ A ≫ presheafInfinityEvaluation a) ≫
          Compact.spaceUniverseDiagram) := by
  let i := Ind.indInclusionPresheaf κ A
  let y := (Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a)
  have hv : i.app (Opposite.op ⦋0⦌) y =
      (yonedaInfinityMap A).app (Opposite.op ⦋0⦌) (ULift.up a) := by
    exact congrArg (fun f : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ PresheafInfinity A ↦
      f.app (Opposite.op ⦋0⦌) (ULift.up a)) (Ind.indYoneda_inclusion κ A)
  have h₀ := Compact.yonedaInfinityMap_evaluationIso a
  rw [← hv] at h₀
  have h := covariantHomComparisonIso i (Ind.indInclusionPresheaf_isFullyFaithful κ A) y ≪≫
    FunctorIso.precomp h₀ ((SSet.uliftFunctor.{u + 2, u + 1}).map i)
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h

end SerrePositivity.InfinityCategories.F2.Presentable
