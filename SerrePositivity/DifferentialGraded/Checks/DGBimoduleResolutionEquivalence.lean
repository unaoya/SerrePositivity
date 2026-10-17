module
public import SerrePositivity.DifferentialGraded.Resolution.BimoduleDerivedEquivalence
public import Mathlib.Data.ZMod.Basic

/-! # 解像度変更の導来bimodule同値と必要仮定の受入検査 -/
@[expose] public section
noncomputable section
universe u v w z t v' w' z' t'
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]
  (B : Type v) [DGCategory A B] (C : Type w) [DGCategory A C]
  (D : Type z) [DGCategory A D] (E : Type t) [DGCategory A E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

-- oppositeと積の本質的全射性にはsmallnessもflatnessも課さない。
example (hF : QuasiEquivalence F) : QuasiEquivalence F.op := quasiEquivalence_op F hF
example (hF : F.onHomotopy.EssSurj) (hG : G.onHomotopy.EssSurj) :
    (F.tensor G).onHomotopy.EssSurj := F.onHomotopy_tensor_essSurj G hF hG

-- 積の準同値性には、交差する二つのHomのK-flat性を明示する。
example (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) :
    QuasiEquivalence (F.tensor G) := quasiEquivalence_tensor F G hF hG hC hD

example [Small.{u} B] [Small.{u} C] [Small.{u} D] [Small.{u} E]
    (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) :
    (derivedBimoduleRestrictionEquivalence A B C D E F G hF hG hC hD).functor =
      derivedBimoduleRestriction A B C D E F G := rfl

-- 指定解像度の左脚には元の対象型のsmallnessを追加しない。
example (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    (ResolutionBimodule.comparisonLeftEquivalence A P Q).functor =
      ResolutionBimodule.comparisonLeft A P Q := rfl

-- 元のHomのflatnessなしで、独立な四つのsource宇宙を比較する。
example [Small.{u} B] [Small.{u} C]
    (P : KFlatDGResolution.{u, v, v'} A B) (Q : KFlatDGResolution.{u, w, w'} A C)
    (R : KFlatDGResolution.{u, v, z'} A B) (S : KFlatDGResolution.{u, w, t'} A C) :
    ResolutionBimodule.DerivedCategory A P Q ≌ ResolutionBimodule.DerivedCategory A R S :=
  ResolutionBimodule.changeEquivalence A P Q R S

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (P R : KFlatDGResolution (ZMod 2) X)
    (Q S : KFlatDGResolution (ZMod 2) Y) :
    ResolutionBimodule.DerivedCategory (ZMod 2) P Q ≌
      ResolutionBimodule.DerivedCategory (ZMod 2) R S :=
  ResolutionBimodule.changeEquivalence (ZMod 2) P Q R S

namespace SerrePositivity.DifferentialGraded
#print axioms closedToOppositeHomotopy
#print axioms closedToOppositeHomotopy_boundary
#print axioms homotopyOppositeFunctor
#print axioms homQuasiIso_op
#print axioms DGFunctor.onHomotopy_op_essSurj
#print axioms quasiEquivalence_op
#print axioms homQuasiIso_tensor
#print axioms DGFunctor.onHomotopy_tensor_essSurj
#print axioms quasiEquivalence_tensor
#print axioms bimoduleToModuleDerived
#print axioms bimoduleToModuleDerived_inverts
#print axioms bimoduleToModuleDerivedIsLocalization
#print axioms rightModuleBimoduleDerivedEquivalence
#print axioms rightModuleBimoduleDerived_fac
#print axioms rightModuleBimoduleDerived_inverse_fac
#print axioms bimoduleRestrictionModuleDerived
#print axioms bimoduleRestrictionModuleDerived_fac
#print axioms bimoduleRestrictionModuleIso
#print axioms derivedBimoduleRestrictionModuleIso
#print axioms bimoduleRestrictionDG_quasiEquivalence
#print axioms derivedBimoduleRestriction_isEquivalence
#print axioms derivedBimoduleRestrictionEquivalence
#print axioms ResolutionBimodule.comparisonLeftEquivalence
#print axioms ResolutionBimodule.comparisonLeftEquivalence_functor
#print axioms ResolutionBimodule.comparisonRightEquivalence
#print axioms ResolutionBimodule.comparisonRightEquivalence_functor
#print axioms ResolutionBimodule.canonicalComparisonEquivalence
#print axioms ResolutionBimodule.changeEquivalence
end SerrePositivity.DifferentialGraded
