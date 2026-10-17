module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleReplacement
public import SerrePositivity.DifferentialGraded.Derived.BimoduleBasic
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.CategoryTheory.Localization.Equivalence

/-! # 積dg圏上の右加群とbimoduleの主導来圏の比較

## 概要
積dg圏上の右加群とbimoduleの主導来圏の比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- 閉零比較の逆を通して、積dg圏上の右加群の主導来圏へ送る。 -/
def bimoduleToModuleDerived :
    BimoduleCategory A B C ⥤ DerivedModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  (rightModuleBimoduleEquivalence A B C).inverse ⋙
    moduleToDerived A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ

lemma bimoduleToModuleDerived_inverts :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy (bimoduleToModuleDerived A B C) := by
  intro M N f hf
  exact moduleToDerived_inverts A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ _
    ((rightModuleBimodule_inverse_quasiIso_iff A B C f).mpr hf)

/-- 閉零比較と準同型の一致から、同じ射のクラスの局所化である。 -/
instance bimoduleToModuleDerivedIsLocalization :
    (bimoduleToModuleDerived A B C).IsLocalization (BimoduleCategory.quasiIso A B C) := by
  let E := rightModuleBimoduleEquivalence A B C
  let Q := moduleToDerived A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  apply Functor.IsLocalization.of_equivalence_source Q
    (moduleQuasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
    (bimoduleToModuleDerived A B C) (BimoduleCategory.quasiIso A B C) E
  · intro M N f hf
    exact (BimoduleCategory.quasiIso A B C).le_isoClosure _
      ((rightModuleBimoduleEquivalence_quasiIso_iff A B C f).mpr hf)
  · exact bimoduleToModuleDerived_inverts A B C
  · exact (Functor.associator E.functor E.inverse Q).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm Q ≪≫ Functor.leftUnitor Q

/-- HomのK-flat性なしで、同じ値ごとの準同型を局所化した二つの表示を比較する。 -/
def rightModuleBimoduleDerivedEquivalence :
    DerivedModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ≌ DerivedBimoduleCategory A B C :=
  Localization.uniq (bimoduleToModuleDerived A B C) (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)

def rightModuleBimoduleDerived_fac :
    bimoduleToModuleDerived A B C ⋙ (rightModuleBimoduleDerivedEquivalence A B C).functor ≅
      bimoduleToDerived A B C :=
  Localization.compUniqFunctor (bimoduleToModuleDerived A B C) (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)

def rightModuleBimoduleDerived_inverse_fac :
    bimoduleToDerived A B C ⋙ (rightModuleBimoduleDerivedEquivalence A B C).inverse ≅
      bimoduleToModuleDerived A B C :=
  Localization.compUniqInverse (bimoduleToModuleDerived A B C) (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)

end SerrePositivity.DifferentialGraded
