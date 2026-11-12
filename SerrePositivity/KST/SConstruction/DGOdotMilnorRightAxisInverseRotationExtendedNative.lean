module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisInverseRotationRealized
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlyingInclusion
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphExtendedNativeComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisNativeSquare
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift

/-!
概要：元実逆回転全比較を同じ恒等 graph の native 商延長へ接続する。
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

/-- 概要：元実逆回転全 realization を同じ恒等 graph の native 商延長へ比較する。
方針：元 Perf 値の全包含を照合し、同じ元 graph の全延長比較を逆向きに合成する。
規約：元 resolved 商・元全 graph・元 cell 始域を保持する。
使われ方：固定 ν 実右面の同じ商射影との全比較への接続。 -/
def dgOdotMilnorRightAxisInverseRotationExtendedNativeComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisInverseRotationRealizedFamily R d))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (MF) ≫ (ρ)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) (Q) (q)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) := by
  let e := dgOdotMilnorRightAxisInverseRotationRealizedNerveComparison R d
  let e' := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e rfl
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleUnderlying_inclusion R (Q) (G)))
  exact e'.trans (dgCellResolvedGraphPerfectExtendedNativeComparison.{u, u + 1} R (B) (Q)
    (DGFunctor.id (B)) (q)).symm
/-- 概要：元実逆回転全比較は同じ恒等 graph の元増大を保って native 商値へ移る。
方針：元指定増大を同じ全包含で後合成し全比較に合成する。
規約：同じ元増大を使用し、指定上下二単体の整合は後続。
使われ方：元 cell 増大の Yoneda 比較と同じ resolved 射影への接続。 -/
def dgOdotMilnorRightAxisInverseRotationAugmentedNativeComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisInverseRotationRealizedFamily R d))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellRestrictedGraphModuleFunctor.{u, u} R (B) (DGFunctor.id (B))) ≫ (ρ)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) (Q) (q)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) :=
  (dgOdotMilnorRightAxisInverseRotationExtendedNativeComparison R d).trans
    (((dgCellResolvedGraphAugmentationNativeComparison.{u, u} R (B)
      (DGFunctor.id (B))).postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) (Q) (q))).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)))
end SerrePositivity.KST.SConstruction
