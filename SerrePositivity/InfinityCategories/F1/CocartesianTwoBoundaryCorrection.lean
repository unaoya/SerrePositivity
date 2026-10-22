module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundaryCoherentOriginal
public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryCorrection

/-!
概要：二次元境界の指定比較同型を保つ、元の全 Hom 作用の補正。
方針：同じ境界への分類先制限の Kan 性で、元の指定 path を持ち上げる。
規約：同じ実境界・全 Hom・元の分類主写像を保持する。
使われ方：指定境界値を固定した実際の fiber 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "a" => HornBoundaryOver.apex 1 σ
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "R" => cocartesianNativeGlobalDiagramRestriction p.val.hom q.val.hom a
local notation "T" => intervalDiagramGlobalDiagramRestriction P Q a
local notation "V" => cocartesianTwoBoundaryCoherentHomComparison j p q
local notation "S" => cocartesianStraighteningHomInterval p q

local instance twoBoundaryCorrectionTargetKan (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex
    ((intervalDiagramLiftOverFunctor P Q).obj (Opposite.op z)) :=
  cocartesianIntervalLiftOverFunctor_obj_kan p q z

/-- 同じ二次元実境界への分類先制限は Kan fibration。 -/
lemma cocartesianTwoBoundaryTargetRestriction_fibration : Fibration T := by
  have : Mono (a).hom :=
    inferInstanceAs (Mono ((boundary 2).ι ≫ (stdSimplex.isoNerve 2).hom))
  have := SimplicialModel.UniverseLift.mono_map (a).hom
  exact intervalDiagramRestriction_fibration _ P Q

/-- 元の指定同型の path を保ち、実際の境界比較と厳密に可換にする。 -/
def cocartesianTwoBoundaryHomCorrection :
    PathCorrectedFunctorSquare T S (R ≫ V)
      (cocartesianTwoBoundaryCoherentHomComparison_originalIso j p q) := by
  haveI := cocartesianTwoBoundaryTargetRestriction_fibration p q
  exact pathCorrectedFunctorSquare T (kanEquivalenceLifting_of_kanFibration T)
    S (R ≫ V) (cocartesianTwoBoundaryCoherentHomComparison_originalIso j p q)

/-- 同じ境界比較に厳密に可換な全 Hom 作用。 -/
def cocartesianTwoBoundaryCorrectedHom := (cocartesianTwoBoundaryHomCorrection j p q).map

/-- 補正した全作用の制限は、元の指定された境界比較そのもの。 -/
lemma cocartesianTwoBoundaryCorrectedHom_comm :
    cocartesianTwoBoundaryCorrectedHom j p q ≫ T = R ≫ V :=
  (cocartesianTwoBoundaryHomCorrection j p q).comm

/-- 同じ指定 path で、元の全分類作用を回収する。 -/
def cocartesianTwoBoundaryCorrectedHomIso :
    FunctorIso (cocartesianTwoBoundaryCorrectedHom j p q) S :=
  (cocartesianTwoBoundaryHomCorrection j p q).exactComponentIso

/-- 補正同型の境界像は、元の指定比較同型に厳密に一致する。 -/
lemma cocartesianTwoBoundaryCorrectedHomIso_boundary :
    F2.functorIsoOfEq ((cocartesianTwoBoundaryCorrectedHomIso j p q).postcomp T)
      (cocartesianTwoBoundaryCorrectedHom_comm j p q) rfl =
      cocartesianTwoBoundaryCoherentHomComparison_originalIso j p q :=
  (cocartesianTwoBoundaryHomCorrection j p q).exactComponentIso_postcomp_normalized

end SerrePositivity.InfinityCategories
