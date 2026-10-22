module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoHornSharedOriginal

/-!
概要：二次内ホーンの全 native Hom 比較を、同じ共有境界比較へ指定同型で制限する。
方針：元の大域 Hom 上の指定三角形を、同値な制限による前合成で反映する。
規約：前合成で元の指定三角形を回収する。
使われ方：二次元境界でホーンと欠けた面の比較を揃える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (cocartesianFiniteHornOver 2 1)
local notation "V" => cocartesianOneBoundaryHomComparison j (stdSimplex.δ (1 : Fin 3) ≫ σ) p q
local notation "N" => cocartesianTwoHornSharedNativeRestriction p q
local notation "T" => cocartesianTwoHornSharedTargetRestriction p q
local notation "H" => cocartesianTwoHornNativeTargetComparison p q

local instance {D : SSet.{u}} (a : D ⟶ nerve (ULift.{u} (Fin 3))) :
    InnerFibration (pullback.fst a q.val.hom) :=
  ⟨innerFibrations.pullback_fst a q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

/-- 元の指定三角形から得る、ホーン比較を共有境界へ制限した同型。 -/
def cocartesianTwoHornSharedComparisonReverseIso : FunctorIso (H ≫ T) (N ≫ V) :=
  homTransportTriangleCoherence
    (cocartesianTwoHornSharedOriginalTargetAction p q)
    (cocartesianTwoHornOriginalTargetAction p q) R T H (N ≫ V)
    (cocartesianTwoHornNativeLiftRestriction_isQCatEquivalence p q)
    (cocartesianTwoHornSharedTargetOriginalIso p q)
    (cocartesianTwoHornNativeTargetComparison_originalIso p q)
    (cocartesianTwoHornSharedNativeOriginalIso p q j)

/-- 同じ全 native ホーン Hom の共有境界への指定自然性。 -/
def cocartesianTwoHornSharedComparisonNaturalityIso : FunctorIso (N ≫ V) (H ≫ T) :=
  (cocartesianTwoHornSharedComparisonReverseIso j p q).symm

/-- 同じ指定自然性を元の大域 Hom へ戻すと、指定三角形そのもの。 -/
lemma cocartesianTwoHornSharedComparisonReverseIso_original :
    (cocartesianTwoHornSharedComparisonReverseIso j p q).precomp R ≪≫
      cocartesianTwoHornSharedNativeOriginalIso p q j =
    (cocartesianTwoHornNativeTargetComparison_originalIso p q).postcomp T ≪≫
      cocartesianTwoHornSharedTargetOriginalIso p q :=
  homTransportTriangleCoherence_identity
    (cocartesianTwoHornSharedOriginalTargetAction p q)
    (cocartesianTwoHornOriginalTargetAction p q) R T H (N ≫ V)
    (cocartesianTwoHornNativeLiftRestriction_isQCatEquivalence p q)
    (cocartesianTwoHornSharedTargetOriginalIso p q)
    (cocartesianTwoHornNativeTargetComparison_originalIso p q)
    (cocartesianTwoHornSharedNativeOriginalIso p q j)

end SerrePositivity.InfinityCategories
