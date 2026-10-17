module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleReplacement
public import SerrePositivity.DifferentialGraded.Derived.BimoduleBasic
public import SerrePositivity.DifferentialGraded.Derived.Restriction
public import SerrePositivity.DifferentialGraded.Functor.Tensor

/-! # 両dg圏の関手に沿う導来bimodule制限

## 概要
既存の積dg圏との同値を用い、全Hom自然な主bimodule圏へ制限を戻す。

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
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

/-- Bᵒᵖ⊗Cのopposite上の右加群を制限するための二重opposite関手。 -/
def bimoduleRestrictionIndex :
    DGFunctor A (DGTensorCategory A Bᵒᵖ C)ᵒᵖᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖᵒᵖ :=
  (F.op.tensor G).op.op

/-- 全次数の二作用を保持する制限関手。 -/
def bimoduleRestriction : BimoduleCategory A D E ⥤ BimoduleCategory A B C :=
  (rightModuleBimoduleEquivalence A D E).inverse ⋙
    moduleRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
      (bimoduleRestrictionIndex A B C D E F G) ⋙
    (rightModuleBimoduleEquivalence A B C).functor

lemma bimoduleRestriction_quasiIso {M N : BimoduleCategory A D E} (f : M ⟶ N)
    (hf : BimoduleCategory.quasiIso A D E f) :
    BimoduleCategory.quasiIso A B C ((bimoduleRestriction A B C D E F G).map f) :=
  (rightModuleBimoduleEquivalence_quasiIso_iff A B C _).2
    (moduleRestriction_quasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (bimoduleRestrictionIndex A B C D E F G) _
      ((rightModuleBimodule_inverse_quasiIso_iff A D E f).2 hf))

/-- 対象ごとの準同型保存から得る、置換不要の導来制限。 -/
def derivedBimoduleRestriction :
    DerivedBimoduleCategory A D E ⥤ DerivedBimoduleCategory A B C :=
  bimoduleDerivedLift A D E
    (bimoduleRestriction A B C D E F G ⋙ bimoduleToDerived A B C) (by
      intro M N f hf
      exact bimoduleToDerived_inverts A B C _ (bimoduleRestriction_quasiIso A B C D E F G f hf))

lemma derivedBimoduleRestriction_fac :
    bimoduleToDerived A D E ⋙ derivedBimoduleRestriction A B C D E F G =
      bimoduleRestriction A B C D E F G ⋙ bimoduleToDerived A B C :=
  bimoduleDerivedLift_fac _ _ _ _ _

end SerrePositivity.DifferentialGraded
