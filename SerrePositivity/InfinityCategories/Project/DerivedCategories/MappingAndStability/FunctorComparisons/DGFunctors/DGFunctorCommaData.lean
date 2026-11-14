module
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPostcompositionChainMap
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
/-!
概要：任意の dg 関手に対し、実比較射を持つ comma の対象と全 Hom の差を構成する。
方針：実入力・実比較対象と、両者を結ぶ同じ閉射を保持する。
規約：射影性・準同型性・Small 性は要求しない。使われ方：普遍余単位と dg gluing。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 実比較射 replacement → F(source) を持つ comma の対象。 -/
structure DGFunctorCommaObject where
  source : C
  replacement : E
  augmentation : ForgetEnrichment.of (Complex R) replacement ⟶
    ForgetEnrichment.of (Complex R) (F.obj source)
variable (X Y : DGFunctorCommaObject R C E F)
/-- 比較正方形の同じ差を与える、全 Hom 複体の間の実鎖写像。 -/
def dgFunctorCommaDifference :
    (homObject R C X.source Y.source ⊞ homObject R E X.replacement Y.replacement) ⟶
      homObject R E X.replacement (F.obj Y.source) :=
  biprod.fst ≫ F.map X.source Y.source ≫
    eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj Y.source)) -
    biprod.snd ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement) Y.augmentation
end SerrePositivity.InfinityCategories.Project.DerivedCategories
