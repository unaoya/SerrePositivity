module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationUnderlyingIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionHomotopy
/-!
概要：同じ厳密切断を通じて、実出力分解と元の関手の基礎空間値を全関手同型で比較する。
方針：実分解圏上の同じ augmentation 同型を前合成し、実二射影の全関手等式を使う。
規約：出力の射影性は不要。使われ方：固定入力の実 D(R) 値 Hom の空間値比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (F : DGFunctor R C (RightModule R PUnit.{1}))
/-- 同じ厳密切断と実 augmentation による、出力分解と元の関手の全空間値比較同型。 -/
def dgModuleOutputResolutionSpaceComparisonIso :
    FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgModuleOutputResolutionInfinity R C PUnit.{1} F) ≫
       (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleOutputInclusionLift.{u, max (u + 1) v, 0} R PUnit.{1})) ≫
          dgHomUnderlyingSpaceInfinity R C)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleOutputOriginalLift R C PUnit.{1} F)) ≫
          dgHomUnderlyingSpaceInfinity R C) := by
  have e := FunctorIso.precomp (dgModuleAugmentationUnderlyingSpaceIso R C F)
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgModuleFunctorResolutionSourceNerveEquivalence R C PUnit.{1} F).inv)
  simp only [← Category.assoc] at e
  rw [← Functor.map_comp, ← Functor.map_comp,
    dgModuleOutputResolution_replacement, dgModuleOutputResolution_original] at e
  simpa only [Functor.map_comp, Category.assoc] using e
end SerrePositivity.InfinityCategories
