module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Coefficients.CoefficientYonedaInverseChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CommonComplexUniverseInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.NativeCochainUniverseComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.CanonicalCoefficientMapping

/-! # 正規化 prism の canonical 係数表示

概要：実係数鎖写像と宇宙輸送の合成を canonical 係数始域同型の逆へ同定する。
方針：Yoneda 同型の実逆射と逆向き宇宙同型を照合し、全 prism に後合成する。
規約：元の Hom 入力・二端点・全区間パラメーターを保持する。
使われ方：実後 cube の区間面を主係数 path の正規化へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

lemma dgGluingNativeCoefficientDomainIso_inv :
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainCoefficientMap R C D M X Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, max (u + 1) v, max u v w,
        max (u + 1) v w} (M.value X.left Y.right)).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientDomainIso R C D M X.left Y.right).inv := by
  have hq : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainCoefficientMap R C D M X Y =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).inv :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso_inv_chainMap R C X.left (M.rightAt Y.right)).symm
  rw [hq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexUniverse_hom_eq_inv]
  rfl

lemma dgGluingNativeNormalizedPrism_canonical_coefficient :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleNormalizedPrism R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientDomainIso R C D M X.left Y.right).inv =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y) := by
  rw [← dgGluingNativeCoefficientDomainIso_inv]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedPrism_coefficient_universe R C D M X Y

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
