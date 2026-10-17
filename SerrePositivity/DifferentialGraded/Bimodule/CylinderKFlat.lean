module
public import SerrePositivity.DifferentialGraded.Bimodule.RightRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.RelativeKFlat
public import SerrePositivity.DifferentialGraded.Module.RestrictionTensor
public import SerrePositivity.DifferentialGraded.Tensor.ModuleCylinderKFlat

/-! # 積dg圏上のcylinderをbimoduleへ移送したときの右相対K-flat性

## 概要
積dg圏上のcylinderをbimoduleへ移送したときの右相対K-flat性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleHomotopy.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma rightModuleBimodule_cylinder_rightRelativeKFlat
    (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
    (hM : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M))) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj
        (modulePrecylinder A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M).I)) := by
  intro c
  have hr := moduleRelativeKFlat_of_iso A B
    (rightModuleBimoduleRightRestrictionIso A B C M c).symm (hM c)
  have ht := moduleRelativeKFlat_tensor A B (dgInterval A) (complexKFlat_interval A)
    (ForgetEnrichment.to (Complex A) ((tensorRightRestriction A B C c).obj M)) hr
  exact moduleRelativeKFlat_of_iso A B
    (rightModuleBimoduleRightRestrictionIso A B C
        (modulePrecylinder A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M).I c ≪≫
      moduleRestrictionTensorIso A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (tensorRightRestrictionInclusion A B C c) (dgInterval A) M) ht

end SerrePositivity.DifferentialGraded
