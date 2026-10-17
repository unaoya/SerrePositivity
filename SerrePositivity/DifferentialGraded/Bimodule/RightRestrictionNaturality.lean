module
public import SerrePositivity.DifferentialGraded.Bimodule.RightRestriction

/-! # 積dg圏表示の右制限比較の射に関する自然性

## 概要
積dg圏表示の右制限比較の射に関する自然性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

def rightModuleBimoduleRightRestrictionNatIso (c : C) :
    (rightModuleBimoduleEquivalence A B C).functor ⋙ BimoduleCategory.evaluation A B C c ≅
      tensorRightRestriction A B C c :=
  NatIso.ofComponents (fun M => rightModuleBimoduleRightRestrictionIso A B C M c) (by
    intro M N f
    apply moduleMorphism_ext
    intro b
    simp only [CategoryTheory.Functor.map_comp, rightModuleBimoduleRightRestrictionIso,
      moduleIsoMk_hom_eval, tensorRightRestriction, moduleRestriction_map_eval]
    have h := (rightModuleBimoduleEvaluationIso A B C b c).hom.naturality f
    exact h)

lemma rightModuleBimoduleRightRestrictionNatIso_app (c : C)
    (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) :
    (rightModuleBimoduleRightRestrictionNatIso A B C c).app M =
      rightModuleBimoduleRightRestrictionIso A B C M c := rfl

end SerrePositivity.DifferentialGraded
