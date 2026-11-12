module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisInverseRotationExtendedNative
public import SerrePositivity.KST.SConstruction.DGCellIdentityGraphYonedaNative
public import SerrePositivity.KST.SConstruction.DGCellYonedaExtensionNative
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlyingInclusion
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphExtendedNativeComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisNativeSquare
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift

/-!
概要：元実逆回転全比較を同じ resolved 射影の元 Yoneda へ接続する。
方針：元二 Perf 関手と元比較の同じ全関手同型を特殊化する。
規約：元 cell 始域・元 resolved 商と元全 Hom を保持する。
使われ方：LT 実右面の全合成比較。固定 ν の三認証は別工程。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "F" => dgOdotMilnorRightAxisQuotientSource R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d
local notation "τ" => dgOdotMilnorRightAxisQuotientComparison R d

local notation "B" => DGOdotGluing R d
local notation "MF" => dgCellResolvedGraphModuleFunctor R (B) (DGFunctor.id (B))
local notation "ρ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "q" => dgOdotMilnorResolvedInclusion R d
local notation "I" => dgFullSubcategoryInclusion R (RightModule R (Q))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R (Q))

/-- 概要：元実逆回転全 realization は同じ resolved 射影の元 Yoneda と全比較される。
方針：同じ元増大、D 正本の対角制限、同じ全代表延長比較を合成する。
規約：元 cell 始域・元 resolved 射影・全 Hom を保持する。
使われ方：元実右面の固定 ν 比較と指定上下二単体への接続。 -/
def dgOdotMilnorRightAxisInverseRotationYonedaComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisInverseRotationRealizedFamily R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((q).comp (dgYoneda R (Q)))) :=
  (dgOdotMilnorRightAxisInverseRotationAugmentedNativeComparison R d).trans
    (((((dgCellIdentityGraphYonedaNativeComparison.{u, u} R (B)).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) (Q) (q))).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))).symm).trans
        (dgCellYonedaProjectionNativeComparison.{u, u} R (B) (Q) (q)))
end SerrePositivity.KST.SConstruction
