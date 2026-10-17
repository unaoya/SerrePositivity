module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestriction

/-! # 両側制限とbimodule値評価の自然比較

## 概要
両側制限とbimodule値評価の自然比較。

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- 積dg圏表示へ移ってからの評価は元のbimodule値と自然同型。 -/
def bimoduleRightModuleEvaluationIso (b : B) (c : C) :
    (rightModuleBimoduleEquivalence A B C).inverse ⋙
        moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c)) ≅
      BimoduleCategory.valueEvaluation A B C b c :=
  Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A B C).inverse
      (rightModuleBimoduleEvaluationIso A B C b c).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightModuleBimoduleEquivalence A B C).counitIso
      (BimoduleCategory.valueEvaluation A B C b c) ≪≫
    Functor.leftUnitor _

variable (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

def bimoduleRestrictionEvaluationIso (b : B) (c : C) :
    bimoduleRestriction A B C D E F G ⋙ BimoduleCategory.valueEvaluation A B C b c ≅
      BimoduleCategory.valueEvaluation A D E (F.obj b) (G.obj c) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (Functor.isoWhiskerLeft
        (moduleRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
          (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (bimoduleRestrictionIndex A B C D E F G))
        (rightModuleBimoduleEvaluationIso A B C b c)) ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (moduleRestrictionEvaluationIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (bimoduleRestrictionIndex A B C D E F G)
        (op (op b, c))) ≪≫
    bimoduleRightModuleEvaluationIso A D E (F.obj b) (G.obj c)

end SerrePositivity.DifferentialGraded
