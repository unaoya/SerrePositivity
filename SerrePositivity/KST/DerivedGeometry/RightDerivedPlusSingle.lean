module

public import SerrePositivity.KST.DerivedGeometry.InjectiveResolutionPlusModel

/-!
概要：bounded below 右導来関手の単一対象上の値を元の injective 分解で計算する。
方針：分解を実際の injective 模型へ持ち上げ、模型上の比較同型と分解の準同型を合成する。
規約：分解の存在や導来比較の存在を仮定として追加しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来単位の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] {X : C} (I : InjectiveResolution X)

/--
概要：通常の injective 分解の零拡張では bounded below 右導来の比較は同型。
方針：同じ分解を injective 対象の圏の複体として構成した模型に照合する。
規約：元の分解の各項と微分を保持する。
使われ方：TT §3、Toën §3.2 の単一対象の右導来切断。
-/
instance rightDerivedPlusUnit_injectiveResolution_isIso :
    IsIso (F.rightDerivedFunctorPlusUnit.app (injectiveResolutionPlus I)) := by
  change IsIso (F.rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι C).mapCochainComplexPlus.obj (injectiveResolutionLiftPlus I)))
  infer_instance

/--
概要：bounded below 右導来の単一対象の像は、その injective 分解への関手適用の導来像と同型。
方針：分解の準同型の像を右導来関手で写し、模型上の右導来比較の逆を合成する。
規約：元の abelian 圏で選んだ任意の実際の分解についての比較。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン非輪状性からの比較。
-/
def rightDerivedPlusSingleIso :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (injectiveResolutionPlus I)) :=
  F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map (injectiveResolutionPlusι I))) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app (injectiveResolutionPlus I))).symm

end SerrePositivity.KST.DerivedGeometry
