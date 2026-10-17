module
public import SerrePositivity.DifferentialGraded.Bimodule.RestrictedRepresentable
public import SerrePositivity.DifferentialGraded.Module.RestrictionTensor

/-! # 積dg圏上の自由加群の右制限

## 概要
積dg圏上の自由加群の右制限。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/BimoduleSemifreeKFlat.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 制限後の生成複体にはHom_C(c₀,c)が現れる。Hom_Bのflat性は用いない。 -/
def restrictedFreeIso (b₀ : B) (c₀ c : C) (K : Complex A) :
    (tensorRightRestriction A B C c).obj
        ((freeAt (A := A) (D := (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
          (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))).obj K) ≅
      (freeAt b₀).obj (K ⊗ (c₀ ⟶[Complex A] c)) :=
  moduleRestrictionTensorIso A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (tensorRightRestrictionInclusion A B C c) K
      (ForgetEnrichment.of (Complex A)
        (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C)))) ≪≫
    (moduleTensorLeftFunctor A B K).mapIso (restrictedRepresentableIso A B C b₀ c₀ c) ≪≫
    tensorModuleAssociatorIso A B K (c₀ ⟶[Complex A] c) (representable A b₀)

end SerrePositivity.DifferentialGraded
