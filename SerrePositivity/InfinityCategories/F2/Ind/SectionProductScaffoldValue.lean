module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductScaffold
public import SerrePositivity.InfinityCategories.F1.Scaffold.UniversalScaffoldFiber

/-!
概要：全単体の切断の大域評価の指定値は、元の単体の初頂点での同じ相対切断評価。
方針：定値な添字の射列の初頂点座標と curry の頂点評価を照合する。
規約：元の大域射の制限との厳密な一致を証明し、各値の同値で代用しない。
使われ方：同じ section product scaffold の fiber 同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B)

/-- 指定された単体上の元の相対切断を、その初頂点の元の fiber に評価する。 -/
def sectionProductValueEvaluation (i : I) (s : TransportSimplexCategory B) :=
  relativeFunctorEvaluate (F.obj i).val.hom
    (SSet.yonedaEquiv.symm s.objDown.val) (stdSimplex.obj₀Equiv.symm 0)

/-- 定値の添字上の始点係数は、同じ初頂点での相対切断評価に一致する。 -/
lemma sectionProductReplacementCoefficient_constant (i : I) (s : TransportSimplexCategory B)
    {n : ℕ} (f : (Δ[n] : SSet.{u}) ⟶
      (strictLeftTransportSectionDiagram F).obj (i, s) |>.obj) :
    sectionProductReplacementCoefficient F
      ⟨(CategoryTheory.Functor.const (Fin (n + 1))).obj (i, s), f⟩ =
      f ≫ sectionProductValueEvaluation F i s ≫ vertexFiberι _ _ := by
  have he := curry_evaluateFunctorAt_vertex (relativeFunctorUncurry f)
    (stdSimplex.obj₀Equiv.symm (0 : Fin (s.objDown.obj.unop.len + 1)))
  change curry (uncurry (f ≫ vertexFiberι _ _)) ≫ _ = _ at he
  rw [curry_uncurry] at he
  rw [sectionProductReplacementCoefficient]
  change lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 _) ≫
    relativeFunctorUncurry f = _
  rw [sectionProductValueEvaluation, relativeFunctorEvaluate_ι]
  exact he.symm

/-- 元の replacement 評価を指定値に制限すると、同じ元の相対切断評価を回収する。 -/
lemma sectionProductReplacementMap_value (i : I) (s : TransportSimplexCategory B) :
    simplicialReplacementConstantLift
      (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) (i, s) ≫
        sectionProductReplacementMap F =
      (sectionProductValueEvaluation F i s ≫ vertexFiberι _ _) ≫
        simplicialReplacementConstantLift (leftFibrationTotalDiagram F) i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change sectionProductReplacementCoefficient F
    ⟨(CategoryTheory.Functor.const (Fin (n + 1))).obj (i, s), SSet.yonedaEquiv.symm x⟩ = _
  rw [sectionProductReplacementCoefficient_constant]
  change SSet.yonedaEquiv.symm x ≫ (sectionProductValueEvaluation F i s ≫ vertexFiberι _ _) =
    SSet.yonedaEquiv.symm ((sectionProductValueEvaluation F i s ≫ vertexFiberι _ _).app _ x)
  exact SSet.yonedaEquiv_symm_comp x _

/-- 同じ大域 weighted 評価の指定値は、同じ fiber 評価と元の定値包含の合成。 -/
lemma sectionProductWeightedEvaluation_value (i : I) (s : TransportSimplexCategory B) :
    simplicialReplacementConstantLift
      (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) (i, s) ≫
        sectionProductWeightedEvaluation F =
      sectionProductValueEvaluation F i s ≫ vertexFiberι _ _ ≫
        weightedNerveConstantLift (leftFibrationTotalDiagram F) i := by
  rw [sectionProductWeightedEvaluation, ← Category.assoc, sectionProductReplacementMap_value,
    Category.assoc, simplicialReplacementConstantLift_tautScaffold]
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
