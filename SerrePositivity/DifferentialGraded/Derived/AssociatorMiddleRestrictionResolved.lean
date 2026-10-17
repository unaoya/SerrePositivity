module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparison
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorNaturality
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleQuasiIso

/-! # 第一中間圏の制限後の指定モデルと結合子の整合性

## 概要
第一中間圏の制限後の指定モデルと結合子の整合性。

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
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
  (S : BimoduleCategory A D E) (R : BimoduleCategory A E T)
  (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "S₀" => BimoduleCategory.underlying A D E S
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LP" => Bimodule.leftRestriction A B C D F P₀
local notation "LPc" => BimoduleCategory.of A B D LP
local notation "RQ" => Bimodule.rightRestriction A C D E F Q₀
local notation "QR" => BimoduleCategory.of A C T (compose A C E T Q₀ R₀)
local notation "SR" => BimoduleCategory.of A D T (compose A D E T S₀ R₀)

/-- 制限後モデルの増大を後因子と合成し、通常の右制限比較を続けた増大射。 -/
def middleRestrictionComposeAugmentation :
    SR ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D T F).obj QR :=
  composeMap A D E T q (𝟙 R) ≫ (composeRightRestrictionIso A C D E T F Q R).hom

omit [DGCategory A B] [Small.{u} B] in
/-- 後因子が右相対K-flatなら、指定増大の準同型性は合成後も保たれる。 -/
lemma middleRestrictionComposeAugmentation_quasiIso
    (hR : Bimodule.rightRelativeKFlat A E T R₀) (hq : BimoduleCategory.quasiIso A D E q) :
    BimoduleCategory.quasiIso A D T
      (middleRestrictionComposeAugmentation A C D E T F Q S R q) := by
  exact (BimoduleCategory.quasiIso A D T).comp_mem _ _
    (composeMap_first_quasiIso A D E T R hR q hq)
    ((BimoduleCategory.quasiIso A D T).of_isIso _)

private lemma prepend_square {V : Type*} [Category* V] {a b c d e f g : V}
    (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d) (t : d ⟶ e)
    (p : a ⟶ f) (α : f ⟶ c) (r : f ⟶ g) (β : g ⟶ e)
    (hn : p ≫ α = u ≫ v) (hs : α ≫ w ≫ t = r ≫ β) :
    u ≫ v ≫ w ≫ t = p ≫ r ≫ β := by
  rw [← Category.assoc u v, ← hn, Category.assoc, hs]

/-- 制限後の任意の増大を使った中間比較も、通常の結合子と可換。 -/
lemma associatorIso_middleRestriction_resolved :
    (associatorIso A B D E T LP S₀ R₀).hom ≫
      middleRestrictionResolvedMap A B C D T F P QR SR
        (middleRestrictionComposeAugmentation A C D E T F Q S R q) =
    composeMap A B E T (middleRestrictionResolvedMap A B C D E F P Q S q) (𝟙 R) ≫
      (associatorIso A B C E T P₀ Q₀ R₀).hom := by
  have hn := associatorIso_naturality A B D E T (𝟙 LPc) q (𝟙 R)
  have hs := associatorIso_middleRestriction A B C D E T F P Q R
  have hm := composeMap_comp A B D T (𝟙 LPc) (𝟙 LPc)
    (composeMap A D E T q (𝟙 R)) (composeRightRestrictionIso A C D E T F Q R).hom
  simp only [Category.id_comp] at hm
  have hc := composeMap_comp A B E T (composeMap A B D E (𝟙 LPc) q)
    (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) (𝟙 R)
  simp only [Category.id_comp] at hc
  dsimp only [middleRestrictionResolvedMap, middleRestrictionComposeAugmentation]
  rw [hm, hc]
  simp only [Category.assoc]
  have hp := prepend_square _ _ _ _ _ _ _ _ hn hs
  convert hp using 1 <;> rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
