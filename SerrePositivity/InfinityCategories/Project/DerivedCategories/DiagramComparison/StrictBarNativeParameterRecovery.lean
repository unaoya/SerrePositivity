module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexEvaluationAtParameter
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeFunctorCocone

/-!
概要：全パラメーターの native 余錐を一つの図式で評価し、元の指定余錐へ戻す。
方針：同じ apex と全 slice セルの等号を、既存の uncurry で戻す。
規約：別の普遍余錐への対象ごとの選択で置き換えない。
使われ方：3b-3 R6、全余錐族の各頂点の余極限性への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 同じ固定射と全セルを持つ slice の二つの族は、同じ join の射を与える。 -/
lemma strictSliceOverUncurry_eq_of_values {K L X : SSet.{u + 1}} {p q : L ⟶ X}
    (hp : p = q) (s : K ⟶ sliceOver p) (t : K ⟶ sliceOver q)
    (h : ∀ (n : SimplexCategoryᵒᵖ) (a : K.obj n),
      (s.app n a).val = (t.app n a).val) :
    sliceOverUncurry s = sliceOverUncurry t := by
  subst q
  have he : s = t := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact Subtype.ext (h n a)
  rw [he]

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 同じ全 apex 関手の固定パラメーター評価は、元の同じ native apex である。 -/
lemma strictBarNativeFunctorApex_atParameter (F : J ⥤ ModuleCategory A PUnit.{1}) :
    strictBarNativeFunctorApex A J ≫ evaluateFunctorAt (ComposableArrows.mk₀ F) =
      SSet.yonedaEquiv.symm
        (dgCoherentBarNativeApex A PUnit.{1} (smallStrictBarDiagram A F)
          (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))) := by
  rw [strictBarNativeFunctorApex, strictFamilyCurry_evaluateAt]
  change lift (SSet.const (ComposableArrows.mk₀ F)) (𝟙 Δ[0]) ≫
      strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
        (strictBarNormalizedFunctor A J ⋙ strictBarClosedVertexFunctor A) = _
  rw [strictSimplexFunctorEvaluation_atParameter]
  congr 1
  apply Simplex.vertexEquiv.injective
  rfl

/-- 全 native 余錐族の固定パラメーター評価は、元の同じ指定 native 余錐に厳密に一致する。 -/
lemma strictBarNativeFunctorCocone_atParameter (F : J ⥤ ModuleCategory A PUnit.{1}) :
    (strictBarNativeFunctorCocone A J).val ≫
        evaluateFunctorAt (ComposableArrows.mk₀ F) =
      (dgCoherentBarNormalizedNativeCocone A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))).val := by
  have h := strictSliceOverUncurry_eq_of_values
    (strictBarNativeFunctorApex_atParameter A J F)
    (strictBarNativeFunctorOverSection A J ≫
      sliceOverPostcomp (strictBarNativeFunctorApex A J)
        (evaluateFunctorAt (ComposableArrows.mk₀ F)))
    (dgCoherentBarNativeOverSection A PUnit.{1} (smallStrictBarDiagram A F)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)))
    (by
      rintro ⟨⟨n⟩⟩ s
      change ((joinStdSimplexIso n 0).hom ≫
          curry (strictBarNativeCellEvaluation A J s.down)) ≫
          evaluateFunctorAt (ComposableArrows.mk₀ F) = _
      rw [Category.assoc, strictFamilyCurry_evaluateAt,
        strictBarNativeCellEvaluation_atParameter]
      rfl)
  rw [sliceOverUncurry_postcomp] at h
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
