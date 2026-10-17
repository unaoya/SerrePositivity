module
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Functor.Opposite

/-! # dg関手に沿う右dg加群の導来制限

## 概要
制限は対象ごとに評価するため任意の準同型を保ち、置換を要さず主局所化へ降りる。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- opposite上の指定dg関手に沿う導来制限。 -/
def moduleDerivedRestriction (F : DGFunctor A Dᵒᵖ Eᵒᵖ) :
    DerivedModuleCategory A E ⥤ DerivedModuleCategory A D :=
  moduleDerivedLift A E (moduleRestriction A D E F ⋙ moduleToDerived A D) (by
    intro M N f hf
    exact moduleToDerived_inverts A D _ (moduleRestriction_quasiIso A D E F f hf))

lemma moduleDerivedRestriction_fac (F : DGFunctor A Dᵒᵖ Eᵒᵖ) :
    moduleToDerived A E ⋙ moduleDerivedRestriction A D E F =
      moduleRestriction A D E F ⋙ moduleToDerived A D := moduleDerivedLift_fac _ _ _ _

/-- 通常向きのdg関手からoppositeを構成して制限する入口。 -/
def dgDerivedRestriction (F : DGFunctor A D E) :
    DerivedModuleCategory A E ⥤ DerivedModuleCategory A D :=
  moduleDerivedRestriction A D E F.op

lemma dgDerivedRestriction_fac (F : DGFunctor A D E) :
    moduleToDerived A E ⋙ dgDerivedRestriction A D E F =
      moduleRestriction A D E F.op ⋙ moduleToDerived A D :=
  moduleDerivedRestriction_fac A D E F.op

end SerrePositivity.DifferentialGraded
