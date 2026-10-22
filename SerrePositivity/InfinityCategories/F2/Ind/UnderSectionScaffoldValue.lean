module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionScaffoldBase
public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionEvaluation
public import SerrePositivity.InfinityCategories.F1.UniversalScaffoldFiber

/-!
概要：大域 under scaffold の指定値での制限は、構成済みの同じ底上の評価射に一致する。
方針：replacement の係数自然性と、元の恒等射での scaffold 評価公式を使う。
規約：各値の同値性だけでなく元の大域射の制限との厳密な一致を証明する。
使われ方：大域分類比較の成分の同値性を、同じ評価射から検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の定値係数への包含は、同じ係数自然変換の replacement と可換。 -/
lemma replacementConstantLift_naturality {I : Type u} [Category.{u} I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) (i : I) :
    simplicialReplacementConstantLift F i ≫ simplicialReplacementMap η =
      η.app i ≫ simplicialReplacementConstantLift G i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  exact SSet.yonedaEquiv_symm_comp x (η.app i)

variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 同じ大域 scaffold の各値は、同じ元の恒等射での評価そのもの。 -/
lemma underSectionScaffold_value (i : I) :
    simplicialReplacementConstantLift (underSectionTotalDiagram p) i ≫
      underSectionScaffold p =
        underSectionEvaluate p i ≫ pullback.fst p (underSectionFiberBase B i) := by
  rw [underSectionScaffold, ← Category.assoc, replacementConstantLift_naturality,
    Category.assoc, simplicialReplacementConstantLift_universalScaffold]
  erw [leftStrictTransportEvaluate_ι]
  change parametrizedSectionsForget p (nerveMap (Under.forget i)) ≫
    (vertexFiberι _ _ ≫ evaluateFunctorAt (strictTransportUnderIdentityVertex i)) = _
  rw [← Category.assoc, parametrizedSectionsForget_ι, underSectionEvaluate_map]
  have hv : (nervePoint (Under.mk (𝟙 i))).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0) = strictTransportUnderIdentityVertex i := by
    dsimp only [nervePoint]
    rw [SSet.yonedaEquiv_symm_zero]
    change PinchedHom.constant (nerveVertex (Under.mk (𝟙 i))) 0 = _
    rw [pinchedConstant_zero]
    rfl
  change _ = _ ≫ (pre (nervePoint (Under.mk (𝟙 i)))).app E ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)
  rw [evaluateFunctorAt_pre, hv]

/-- 元の大域 scaffold を指定添字で制限した、同じ元の引き戻しへの射。 -/
def underSectionScaffoldValueMap (i : I) :
    underSectionFamily p i ⟶ pullback p (underSectionFiberBase B i) :=
  pullback.lift
    (simplicialReplacementConstantLift (underSectionTotalDiagram p) i ≫ underSectionScaffold p)
    (underSectionFamilyProjection p i) (by
      rw [underSectionScaffold_value, Category.assoc, pullback.condition,
        ← Category.assoc, underSectionEvaluate_projection])

/-- 元の大域射の制限は、既存の底上の同じ評価射と厳密に一致する。 -/
lemma underSectionScaffoldValueMap_eq (i : I) :
    underSectionScaffoldValueMap p i = underSectionEvaluate p i := by
  apply pullback.hom_ext
  · rw [underSectionScaffoldValueMap, pullback.lift_fst, underSectionScaffold_value]
  · rw [underSectionScaffoldValueMap, pullback.lift_snd, underSectionEvaluate_projection]

/-- 元の大域射を各値に制限した射自体が、全境界を持ち上げる。 -/
lemma underSectionScaffoldValueMap_trivialKanFibration [LeftFibration p] (i : I) :
    TrivialKanFibration (underSectionScaffoldValueMap p i) := by
  rw [underSectionScaffoldValueMap_eq]
  exact underSectionEvaluate_trivialKanFibration p i

end SerrePositivity.InfinityCategories.F2.Ind
