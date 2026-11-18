module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexCochainAugmentationZero
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexAugmentationZero
/-!
概要：指定された標準単体増大写像をMoore零次射影の生成元で評価する。
方針：零次Moore同型と既存の単体増大写像の値を使う。
規約：A05aの最後の切断の証明の分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 元のMoore射影の零次生成元は同じ増大写像で単位へ写る。 -/
theorem standardParameterAugmentation_moore_generator (A : Type u) [CommRing A]
    (n : SimplexCategory)
    (a : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)).obj (Opposite.op ⦋0⦌)) :
    let W := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⋙ ModuleCat.free A
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom.f 0
      ((((normalizedMooreComplex (ModuleCat A)).obj W).extendXIso
        ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) rfl).inv
        ((PInftyToNormalizedMooreComplex W).f 0 (ModuleCat.freeMk a))) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  let W := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⋙ ModuleCat.free A
  have hπ : (PInftyToNormalizedMooreComplex W).f 0 = (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv := by
    apply (cancel_epi (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).hom).1
    rw [Iso.hom_inv_id]
    exact congrArg (fun f => f.f 0) (splitMonoInclusionOfMooreComplexMap W).id
  apply (ModuleCat.mono_iff_injective (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).mp inferInstance
  rw [Iso.inv_hom_id_apply]
  erw [hπ]
  exact (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainAugmentation_zero_apply A n _).trans
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainAugmentation_zero A n a.down)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
