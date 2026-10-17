module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleReplacement
public import Mathlib.Data.ZMod.Basic

/-! # K-flat cylinder・ホモトピー同一視・導来置換関手の監査

## 概要
K-flat cylinder・ホモトピー同一視・導来置換関手の監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

example : complexKFlat A (dgInterval A) := complexKFlat_interval A

example (K : Complex A) (M : RightModule A B) (N : LeftModule A B) :
    BalancedTensor.obj A B (tensorModule K M) N ≅ K ⊗ BalancedTensor.obj A B M N :=
  BalancedTensor.tensorModuleIso A B K M N

example (M : ModuleCategory A B)
    (hM : moduleRelativeKFlat A B (ForgetEnrichment.to (Complex A) M)) :
    moduleRelativeKFlat A B
      (ForgetEnrichment.to (Complex A) (modulePrecylinder A B M).I) :=
  modulePrecylinder_relativeKFlat A B M hM

example (hC : localHomKFlat A C) :
    DerivedBimoduleCategory A B C ⥤ DerivedRightKFlatBimoduleCategory A B C :=
  derivedRightKFlatReplacement A B C hC

example (hC : localHomKFlat A C) :
    bimoduleToDerived A B C ⋙ derivedRightKFlatReplacement A B C hC =
      rightKFlatReplacementFunctor A B C hC := derivedRightKFlatReplacement_fac A B C hC

example (hC : localHomKFlat A C) {M N P : BimoduleCategory A B C} (f : M ⟶ N) (g : N ⟶ P) :
    (rightKFlatReplacementFunctor A B C hC).map (f ≫ g) =
      (rightKFlatReplacementFunctor A B C hC).map f ≫
        (rightKFlatReplacementFunctor A B C hC).map g :=
  (rightKFlatReplacementFunctor A B C hC).map_comp f g

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [Small.{0} B] [Small.{0} C] (hC : localHomKFlat (ZMod 2) C) :
    DerivedBimoduleCategory (ZMod 2) B C ⥤ DerivedRightKFlatBimoduleCategory (ZMod 2) B C :=
  derivedRightKFlatReplacement (ZMod 2) B C hC

#print axioms BalancedTensor.tensorModuleHom
#print axioms BalancedTensor.tensorModuleInv
#print axioms BalancedTensor.ι_tensorModuleHom
#print axioms BalancedTensor.ι_tensorModuleInv
#print axioms BalancedTensor.tensorModuleIso
#print axioms complexKFlat_interval
#print axioms moduleRelativeKFlat_tensor
#print axioms modulePrecylinder_relativeKFlat
#print axioms rightModuleBimodule_cylinder_rightRelativeKFlat
#print axioms rightKFlatOfModule
#print axioms rightKFlatOfModuleMap
#print axioms rightKFlatOfModuleMap_id
#print axioms rightKFlatOfModuleMap_comp
#print axioms rightKFlat_equalizes_source_boundary
#print axioms rightKFlat_map_eq_of_source_homotopy
#print axioms rightModuleBimodule_inverse_quasiIso_iff
#print axioms bimoduleSourceProjectiveResolution
#print axioms rightKFlatReplacementMap
#print axioms rightKFlatReplacementMap_id
#print axioms rightKFlatReplacementMap_comp
#print axioms rightKFlatReplacementFunctor
#print axioms rightKFlatReplacementFunctor_inverts
#print axioms derivedRightKFlatReplacement
#print axioms derivedRightKFlatReplacement_fac
