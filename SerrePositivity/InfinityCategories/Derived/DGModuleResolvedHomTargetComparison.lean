module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationHomTargetSpace
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationProjections
public import SerrePositivity.InfinityCategories.Derived.DGFullSubcategoryHomTarget
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetSpaceComparison
/-!
概要：元の実導来関手の Hom 試験を、生の入力像の同じ Hom 試験へ全関手同型で比較する。
方針：同じ augmentation の空間値同型を実入力切断に戻し、充満部分圏と F1 へ照合する。
規約：生の出力の射影性も入力の Small 性も不要。使われ方：一般 kernel の有限極限保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 元の実導来関手と同じ表現可能 Hom の全関手比較。 -/
def dgModuleResolvedHomTargetSpaceIso
    (T : RightModule R E)
    (hT : moduleHomotopicallyProjective R E (ForgetEnrichment.of (Complex R) T)) :
    FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgModuleResolvedInfinity R C E F ≫ dgNerve.map
          (dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E))) ≫
          dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (dgNerve.map F) ≫
        dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T) := by
  let S := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  have e := (dgModuleAugmentationHomTargetSpaceIso R C E F T hT).precomp
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map S)
  simp only [← Category.assoc, ← Functor.map_comp] at e
  dsimp only [S] at e
  simp only [Category.assoc] at e
  rw [dgModuleResolvedSection_augmentationSource, dgModuleResolvedSection_augmentationTarget] at e
  exact e
/-- 元の実導来関手と同じ表現可能 Hom の全関手比較。 -/
def dgModuleResolvedRepresentableHomSpaceIso (T : SemifreeDGModules R E) :
    FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgModuleResolvedInfinity R C E F) ≫
          dgHomTargetUnderlyingSpaceInfinity R (SemifreeDGModules R E) T)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (dgNerve.map F) ≫
        dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T.val) := by
  have e := dgModuleResolvedHomTargetSpaceIso R C E F T.val
    (dgSemifreeModule_isProjective R E T)
  simpa only [Functor.map_comp, Category.assoc,
    dgFullSubcategoryHomTargetUnderlyingSpaceInfinity] using! e
/-- 元の実導来関手と同じ表現可能 Hom の全関手比較。 -/
def dgModuleResolvedF1HomSpaceIso (T : SemifreeDGModules R E) :
    FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgModuleResolvedInfinity R C E F) ≫
          dgCosliceYonedaSpaceInfinity (dgModuleDerivedInfinityCategory R E) (Simplex.vertex T))
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (dgNerve.map F) ≫
        dgCosliceYonedaSpaceInfinity (dgModuleNerve R E) (Simplex.vertex T.val)) :=
  ((dgHomTargetSpaceComparisonIso R (SemifreeDGModules R E) T).precomp
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgModuleResolvedInfinity R C E F))).symm ≪≫
    dgModuleResolvedRepresentableHomSpaceIso R C E F T ≪≫
      (dgHomTargetSpaceComparisonIso R (RightModule R E) T.val).precomp
        ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (dgNerve.map F))
end SerrePositivity.InfinityCategories
