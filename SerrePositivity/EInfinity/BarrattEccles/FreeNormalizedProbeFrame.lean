module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeHomComparison
public import SerrePositivity.EInfinity.BarrattEccles.FreeForgetHomFrames

/-!
# 元の正規化 probe frame の実自由 E 代数像

概要：同じ QX⊗N(Δ•) を自由 E 代数へ送り、同じ FQX へ全自然に増大する。
方針：元の全 augmentation の自由関手像を両変数の射に自然に束ねる。
規約：元の自由関手・probe・augmentation を保つ。
使われ方：標準自由単位と実正規化 Hom の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def freeNormalizedProbeFrame : Complex A ⥤ (SimplexCategory ⥤ (operad A).Algebra) :=
  _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A ⋙
    (Functor.whiskeringRight SimplexCategory (Complex A) (operad A).Algebra).obj
      (operad A).freeAlgebraFunctor

def freeNormalizedProbeAugmentation :
    freeNormalizedProbeFrame A ⟶ freeProbeFunctor A ⋙ Functor.const SimplexCategory where
  app X :=
    { app n := (operad A).freeAlgebraFunctor.map
        (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X).app n)
      naturality n m f := by
        change (operad A).freeAlgebraFunctor.map
            (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).obj X).map f) ≫
          (operad A).freeAlgebraFunctor.map
            (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X).app m) =
          (operad A).freeAlgebraFunctor.map
            (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X).app n) ≫ 𝟙 _
        rw [Category.comp_id, ← Functor.map_comp]
        exact congrArg (operad A).freeAlgebraFunctor.map
          ((((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X).naturality f).trans
            (Category.comp_id _)) }
  naturality X Y f := by
    apply NatTrans.ext
    funext n
    change (operad A).freeAlgebraFunctor.map
        (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).map f).app n) ≫
      (operad A).freeAlgebraFunctor.map
        (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app Y).app n) =
      (operad A).freeAlgebraFunctor.map
        (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X).app n) ≫
      (operad A).freeAlgebraFunctor.map ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).map f)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (operad A).freeAlgebraFunctor.map
      (congr_app ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).naturality f) n)

end SerrePositivity.EInfinity.BarrattEccles
