module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugPrismReindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
/-!
概要：同じ実 augmentation 単体の全自然性から、dg nerve と標準一単体の積の実写像を作る。
方針：対象だけを共通宇宙へ上げ、同じ単体族と同じ実両端を使う。
規約：入力対象の Small 性や元の出力の射影性を仮定しない。
使われ方：一般commaの実 augmentation の全単体自然性。
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
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
/-- 対象のみを共通宇宙へ上げた、同じ実比較対象射影。 -/
def dgCommaAugmentationSourceLift :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, max u v} E) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, max u v} R E)
/-- 対象のみを共通宇宙へ上げた、元の同じ入力像。 -/
def dgCommaAugmentationTargetLift :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, max u v} E) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R C E F).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, max u v} R E)
/-- 同じ実 augmentation の全単体族から構成した、標準一単体との積からの実写像。 -/
def dgCommaAugmentationNervePrism :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) ⊗ Δ[1] ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, max u v} E) where
  app _ := ↾fun s ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R C E F s.1
    (SSet.stdSimplex.objEquiv s.2).toOrderHom).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, max u v} R E)
  naturality _ _ f := by
    ext s
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R C E F
      (s.1.pullback f.unop.toOrderHom)
      ((SSet.stdSimplex.objEquiv s.2).toOrderHom.comp f.unop.toOrderHom)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, max u v} R E) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R C E F s.1
        (SSet.stdSimplex.objEquiv s.2).toOrderHom).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, max u v} R E)).pullback
            f.unop.toOrderHom
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback _ _ _
/-- 実 prism 写像の零端点は、同じ実比較対象射影の dg nerve 写像。 -/
lemma dgCommaAugmentationNervePrism_zero :
    SSet.ι₀ ≫ dgCommaAugmentationNervePrism R C E F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCommaAugmentationSourceLift R C E F) := by
  ext n s
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R C E F s (OrderHom.const _ (0 : Fin 2))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, max u v} R E) =
    s.map (dgCommaAugmentationSourceLift R C E F)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_zero]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp s.toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, max u v} R E)).symm
/-- 実 prism 写像の一端点は、元の同じ入力像の dg nerve 写像。 -/
lemma dgCommaAugmentationNervePrism_one :
    SSet.ι₁ ≫ dgCommaAugmentationNervePrism R C E F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCommaAugmentationTargetLift R C E F) := by
  ext n s
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R C E F s (OrderHom.const _ (1 : Fin 2))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, max u v} R E) =
    s.map (dgCommaAugmentationTargetLift R C E F)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_one]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp s.toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, max u v} R E)).symm
/-- 元の同じ augmentation が与える、実 dg nerve 写像の間の単体的ホモトピー。 -/
def dgCommaAugmentationNerveHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCommaAugmentationSourceLift R C E F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCommaAugmentationTargetLift R C E F)) where
  h := dgCommaAugmentationNervePrism R C E F
  h₀ := dgCommaAugmentationNervePrism_zero R C E F
  h₁ := dgCommaAugmentationNervePrism_one R C E F
  rel := by
    ext n s
    exact False.elim s.1.2
end SerrePositivity.InfinityCategories.Project.DerivedCategories
