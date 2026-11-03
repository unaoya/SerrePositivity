module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor
public import Mathlib.Data.ZMod.Basic

/-! # 任意bimoduleへの積dg圏上semifree解像度の受入監査

## 概要
任意bimoduleへの積dg圏上semifree解像度の受入監査。

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
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

example : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ≌ BimoduleCategory A B C :=
  rightModuleBimoduleEquivalence A B C

example (b : B) (c : C) :
    (rightModuleBimoduleEquivalence A B C).functor ⋙
        BimoduleCategory.valueEvaluation A B C b c ≅
      moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c)) :=
  rightModuleBimoduleEvaluationIso A B C b c

example (M : BimoduleCategory A B C) : Nonempty (BimoduleSemifreeResolution A B C M) :=
  exists_semifree_bimodule_resolution A B C M

example (M : BimoduleCategory A B C) :
    moduleSemifree A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (bimoduleCanonicalSemifreeResolution A B C M).source :=
  (bimoduleCanonicalSemifreeResolution A B C M).semifree

example (M : BimoduleCategory A B C) (b : B) (c : C) :
    QuasiIso ((BimoduleCategory.valueEvaluation A B C b c).map
      (bimoduleCanonicalSemifreeResolution A B C M).π) :=
  (bimoduleCanonicalSemifreeResolution A B C M).value_quasiIso b c

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [Small.{0} B] [Small.{0} C] (M : BimoduleCategory (ZMod 2) B C) :
    Nonempty (BimoduleSemifreeResolution (ZMod 2) B C M) :=
  exists_semifree_bimodule_resolution (ZMod 2) B C M

example {M : BimoduleCategory A B C} (P Q : BimoduleSemifreeResolution A B C M) :
    BimoduleCategory.quasiIso A B C (P.comparison Q) := P.comparison_quasiIso Q

example {M : BimoduleCategory A B C} (P Q : BimoduleSemifreeResolution A B C M) :
    (bimoduleToDerived A B C).map (P.comparison Q) ≫ (bimoduleToDerived A B C).map Q.π =
      (bimoduleToDerived A B C).map P.π := P.comparison_fac Q

example {M : BimoduleCategory A B C} (P Q R : BimoduleSemifreeResolution A B C M) :
    P.comparisonIso Q ≪≫ Q.comparisonIso R = P.comparisonIso R := P.comparisonIso_trans Q R

#print axioms rightModuleBimoduleEquivalence
#print axioms rightModuleBimoduleEvaluationIso
#print axioms rightModuleBimoduleEquivalence_quasiIso_iff
#print axioms BimoduleSemifreeResolution
#print axioms BimoduleSemifreeResolution.obj
#print axioms BimoduleSemifreeResolution.semifree
#print axioms BimoduleSemifreeResolution.value_quasiIso
#print axioms bimoduleCanonicalSemifreeResolution
#print axioms exists_semifree_bimodule_resolution
#print axioms BimoduleSemifreeResolution.toProjectiveResolution
#print axioms BimoduleSemifreeResolution.augmentation_fac
#print axioms BimoduleSemifreeResolution.comparison
#print axioms BimoduleSemifreeResolution.comparison_quasiIso
#print axioms BimoduleSemifreeResolution.map_eq_of_source_homotopy
#print axioms BimoduleSemifreeResolution.comparison_fac
#print axioms BimoduleSemifreeResolution.comparison_unique
#print axioms BimoduleSemifreeResolution.comparisonIso
#print axioms BimoduleSemifreeResolution.comparisonIso_self
#print axioms BimoduleSemifreeResolution.comparisonIso_trans
