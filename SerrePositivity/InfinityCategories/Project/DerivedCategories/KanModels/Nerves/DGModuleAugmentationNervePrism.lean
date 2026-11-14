module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationPrismReindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGUniverseLift
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
/-!
概要：同じ実 augmentation 単体の全自然性から、dg nerve と標準一単体の積の実写像を作る。
方針：対象だけを共通宇宙へ上げ、同じ単体族と同じ実両端を使う。
規約：入力対象の Small 性や元の出力の射影性を仮定しない。
使われ方：一般出力分解の実 augmentation の全単体自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory Opposite
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 対象のみを共通宇宙へ上げた、同じ実半自由出力射影。 -/
def dgModuleAugmentationSourceLift :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) w, v} (RightModule R E)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))
/-- 対象のみを共通宇宙へ上げた、元の同じ入力像。 -/
def dgModuleAugmentationTargetLift :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) w, v} (RightModule R E)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))
/-- 同じ実 augmentation の全単体族から構成した、標準一単体との積からの実写像。 -/
def dgModuleAugmentationNervePrism :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) ⊗ Δ[1] ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) w, v} (RightModule R E)) where
  app _ := ↾fun s ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex R C E F s.1
    (SSet.stdSimplex.objEquiv s.2).toOrderHom).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))
  naturality _ _ f := by
    ext s
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex R C E F
      (s.1.pullback f.unop.toOrderHom)
      ((SSet.stdSimplex.objEquiv s.2).toOrderHom.comp f.unop.toOrderHom)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E)) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex R C E F s.1
        (SSet.stdSimplex.objEquiv s.2).toOrderHom).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))).pullback
            f.unop.toOrderHom
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex_pullback]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback _ _ _
/-- 実 prism 写像の零端点は、同じ実半自由出力射影の dg nerve 写像。 -/
lemma dgModuleAugmentationNervePrism_zero :
    SSet.ι₀ ≫ dgModuleAugmentationNervePrism R C E F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleAugmentationSourceLift R C E F) := by
  ext n s
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex R C E F s (OrderHom.const _ (0 : Fin 2))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E)) =
    s.map (dgModuleAugmentationSourceLift R C E F)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex_zero]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp s.toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))).symm
/-- 実 prism 写像の一端点は、元の同じ入力像の dg nerve 写像。 -/
lemma dgModuleAugmentationNervePrism_one :
    SSet.ι₁ ≫ dgModuleAugmentationNervePrism R C E F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleAugmentationTargetLift R C E F) := by
  ext n s
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex R C E F s (OrderHom.const _ (1 : Fin 2))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E)) =
    s.map (dgModuleAugmentationTargetLift R C E F)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex_one]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp s.toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))).symm
/-- 元の同じ augmentation が与える、実 dg nerve 写像の間の単体的ホモトピー。 -/
def dgModuleAugmentationNerveHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleAugmentationSourceLift R C E F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleAugmentationTargetLift R C E F)) where
  h := dgModuleAugmentationNervePrism R C E F
  h₀ := dgModuleAugmentationNervePrism_zero R C E F
  h₁ := dgModuleAugmentationNervePrism_one R C E F
  rel := by
    ext n s
    exact False.elim s.1.2
end SerrePositivity.InfinityCategories.Project.DerivedCategories
