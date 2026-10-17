module
public import SerrePositivity.DifferentialGraded.Bimodule.Isomorphism

/-! # 値の全Hom自然性から右加群同型族をbimodule同型へ束ねる

## 概要
値の全Hom自然性から右加群同型族をbimodule同型へ束ねる。

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
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C]

lemma isoFamily_naturality_of_values {M N : BimoduleCategory A B C}
    (a : ∀ c, (evaluation A B C c).obj M ≅ (evaluation A B C c).obj N)
    (h : ∀ b c c', ((underlying A B C M).leftAt b).map c c' ≫
      homPostcompose ((underlying A B C M).value b c)
        ((moduleEvaluation A B b).map (a c').hom) =
      ((underlying A B C N).leftAt b).map c c' ≫
        homPrecompose ((moduleEvaluation A B b).map (a c).hom)
          ((underlying A B C N).value b c')) (c c' : C) :
    (underlying A B C M).map c c' ≫
      moduleHomPostcompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C M).rightAt c') ((underlying A B C N).rightAt c') (a c').hom =
    (underlying A B C N).map c c' ≫
      moduleHomPrecompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c) ((underlying A B C N).rightAt c') (a c).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  have hh := h b c c'
  change (_ ≫ moduleHomπ A B _ _ b) ≫ _ = (_ ≫ moduleHomπ A B _ _ b) ≫ _ at hh
  exact (Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _))

/-- 右加群同型族の左作用との全次数自然性を、値のHom複体で確認して束ねる。 -/
def isoOfValueFamily {M N : BimoduleCategory A B C}
    (a : ∀ c, (evaluation A B C c).obj M ≅ (evaluation A B C c).obj N)
    (h : ∀ b c c', ((underlying A B C M).leftAt b).map c c' ≫
      homPostcompose ((underlying A B C M).value b c)
        ((moduleEvaluation A B b).map (a c').hom) =
      ((underlying A B C N).leftAt b).map c c' ≫
        homPrecompose ((moduleEvaluation A B b).map (a c).hom)
          ((underlying A B C N).value b c')) : M ≅ N :=
  isoOfFamily A B C a (isoFamily_naturality_of_values A B C a h)

@[simp]
lemma isoOfValueFamily_hom_eval {M N : BimoduleCategory A B C} (a) (h) (c : C) :
    (evaluation A B C c).map (isoOfValueFamily A B C (M := M) (N := N) a h).hom =
      (a c).hom := rfl

end SerrePositivity.DifferentialGraded.BimoduleCategory
