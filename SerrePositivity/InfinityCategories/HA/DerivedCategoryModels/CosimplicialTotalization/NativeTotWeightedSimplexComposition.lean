module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedSimplex

/-!
概要：元のweighted Totセルの全HA写像は元の恒等・合成を保つ。
方針：既存StrictSimplexMapの全頂点成分の外延性と閉零射の同じ合成則。
規約：IS-W2 D01の既存構成の単位・合成則。高次自然性は元の指定写像から保つ。
使われ方：HA 1.2.4、同じセルの全パラメータ族の構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {A : Type u} [CommRing A]

/-- 同じ元の恒等図式射は、全HA成分に可換する恒等写像。 -/
theorem nativeTotWeightedSimplexMap_id (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedSimplexMap (𝟙 X) σ = StrictSimplexMap.id (nativeTotWeightedSimplexData X σ) := by
  apply StrictSimplexMap.ext
  intro i
  induction i using Fin.cases
  case zero =>
    change closedHomEquiv A (Complex A) _ _
      ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((productTotalFunctor A).map (𝟙 X))) = _
    rw [(productTotalFunctor A).map_id, (_root_.SerrePositivity.ComplexLimits.complexToClosed A).map_id]
    exact closedHom_id _
  case succ i =>
    change closedHomEquiv A (Complex A) _ _
      ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 (X.obj (AsSmall.down.obj (σ.obj i))))) = _
    rw [(_root_.SerrePositivity.ComplexLimits.complexToClosed A).map_id]
    exact closedHom_id _

/-- 同じ元の図式射の合成は、同じ全HA写像の合成。 -/
theorem nativeTotWeightedSimplexMap_comp {X Y Z : CosimplicialObject (Complex A)}
    (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedSimplexMap (f ≫ g) σ =
      (nativeTotWeightedSimplexMap f σ).comp (nativeTotWeightedSimplexMap g σ) := by
  apply StrictSimplexMap.ext
  intro i
  apply Subtype.ext
  induction i using Fin.cases
  case zero =>
    change (closedHomEquiv A (Complex A) _ _
      ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((productTotalFunctor A).map (f ≫ g)))).val =
      compose A (closedHomEquiv A (Complex A) _ _
        ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((productTotalFunctor A).map g))).val
        (closedHomEquiv A (Complex A) _ _
          ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((productTotalFunctor A).map f))).val (zero_add 0)
    rw [(productTotalFunctor A).map_comp, (_root_.SerrePositivity.ComplexLimits.complexToClosed A).map_comp, closedHom_comp]
  case succ i =>
    change (closedHomEquiv A (Complex A) _ _
      ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((f ≫ g).app (AsSmall.down.obj (σ.obj i))))).val =
      compose A (closedHomEquiv A (Complex A) _ _
        ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (g.app (AsSmall.down.obj (σ.obj i))))).val
        (closedHomEquiv A (Complex A) _ _
          ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (f.app (AsSmall.down.obj (σ.obj i))))).val (zero_add 0)
    rw [NatTrans.comp_app, (_root_.SerrePositivity.ComplexLimits.complexToClosed A).map_comp, closedHom_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
