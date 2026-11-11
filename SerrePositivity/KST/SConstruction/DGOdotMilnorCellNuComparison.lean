module
public import SerrePositivity.KST.SConstruction.DGKNativeNuNaturality
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCellVerdier

/-!
概要：実平坦核包含・cell 商射影の二辺を同じ固定 ν 二辺へ全自然に比較する。
方針：元の strict dg 二辺に構成済みの Yoneda・評価自然性を適用する。
規約：同じ核・cell 始域・resolved 商・D-21 の実完備化を保持する。
使われ方：d④ の実零化面の完備化付き認証と指定境界比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "T" => DGCategoryCellResolution.Source R (B)
local notation "P" => dgQuotientImage R
  (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (B) (P)
local notation "Q" => DGQuotient.QuotientObject (T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B) (P))
local notation "I" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R (B) (P)
local notation "j" => DGQuotient.inclusion R (T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B) (P))
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (B) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (T) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (B)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (Q) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_isDGPretriangulated R (B) (P)

/-- 概要：同じ実平坦核包含の固定 ν 完全射。
方針：元の厳密 S 辺を同じ固定界面に渡す。
規約：元の核包含を保持する。使われ方：零化面の左辺の型付き回収。 -/
abbrev dgOdotMilnorFlatKernelExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d))
    (dgKInputStableValue R (dgOdotMilnorCellInput R d)) :=
  dgKInputNuMap R (dgOdotMilnorFlatKernelInputMap R d)

/-- 概要：同じ実核包含の native 辺と固定 ν 辺の全比較。
方針：Milnor 条件から構成した同じ native 頂点同値で自然性を照合する。
規約：元の包含の全 Hom 作用を保持する。使われ方：実面の下境界。 -/
def dgOdotMilnorFlatKernelNuComparison (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorSourceKernelNativeValueEquivalence R d h).hom ≫
      (dgOdotMilnorFlatKernelExactMap R d).hom)
    ((dgOdotMilnorCellKernelInclusion R d).hom ≫
      (dgOdotMilnorCellMiddleNativeValueEquivalence R d).hom) := by
  letI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (K) := dgOdotMilnorSourceKernel_isDGPretriangulated R d h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKNativeValueComparison R (K) ≫
    (dgKNativeInputExactMap R (K) (T) (I)).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) ≫ dgKNativeValueComparison R (T))
  exact dgKNativeNuNaturality R (K) (T) (I)

/-- 概要：同じ cell 商射影の native 完備化と固定 ν 辺の全比較。
方針：同じ元の商包含の自然性を適用する。
規約：終域比較は既構成の D-21 の実 c そのもの。使われ方：実面の右境界。 -/
def dgOdotMilnorCellProjectionNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorCellMiddleNativeValueEquivalence R d).hom ≫
      (dgOdotMilnorCellProjectionExactMap R d).hom)
    ((dgOdotMilnorCellNativeProjection R d).hom ≫ (dgOdotMilnorCompletion R d).hom) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKNativeValueComparison R (T) ≫
    (dgKNativeInputExactMap R (T) (Q) (j)).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (j) ≫ dgKNativeValueComparison R (Q))
  exact dgKNativeNuNaturality R (T) (Q) (j)

end SerrePositivity.KST.SConstruction
