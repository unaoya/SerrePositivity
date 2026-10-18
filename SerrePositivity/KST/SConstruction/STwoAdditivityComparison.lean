module
public import SerrePositivity.KST.SConstruction.ObjectSConstruction
public import SerrePositivity.KST.SConstruction.SOneExact
public import SerrePositivity.KST.SConstruction.MultiRealization
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-! # S₂ の subobject・middle・quotient と加法性の比較射
概要：cofiber 列の模型 S₂C の三つの評価を完全関手として定義する。
方針：三つの面から S₁ への制限と既存の S₁ 比較を使う。
規約：比較射の同値性は定義に含めない。使われ方：McCarthy 加法性と正の Ω 条件の補題。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 概要：cofiber 列の三つの対象への完全関手の自然変換。
方針：S₂ の面と S₁ 比較を合成する。
規約：i=2 が subobject、i=1 が middle、i=0 が quotient。使われ方：加法性の二つの脚。 -/
def sTwoFaceComparisonNat (i : Fin 3) : sEndofunctor.{u} 2 ⟶ 𝟭 StableModel.{u} :=
  sEndofunctorMap (SimplexCategory.δ i).toOrderHom ≫ stableSOneComparisonNat

/-- 概要：cofiber 列から subobject を取る完全関手の成分。
方針：δ₂ が選ぶ (0,1) に制限する。
規約：零対象の選択を保存する仮定は不要。使われ方：McCarthy の subobject の射。 -/
def sTwoSubobject (X : StableModel.{u}) : (sEndofunctor 2).obj X ⟶ X :=
  (sTwoFaceComparisonNat 2).app X

/-- 概要：cofiber 列から middle を取る完全関手の成分。
方針：δ₁ が選ぶ (0,2) に制限する。
規約：cofiber 列の拡張データを保つ。使われ方：加法性の中間項。 -/
def sTwoMiddle (X : StableModel.{u}) : (sEndofunctor 2).obj X ⟶ X :=
  (sTwoFaceComparisonNat 1).app X

/-- 概要：cofiber 列から quotient を取る完全関手の成分。
方針：δ₀ が選ぶ (1,2) に制限する。
規約：安定な入力について自然。使われ方：McCarthy の quotient の射。 -/
def sTwoQuotient (X : StableModel.{u}) : (sEndofunctor 2).obj X ⟶ X :=
  (sTwoFaceComparisonNat 0).app X

/-- 概要：任意の空間値関手を subobject・quotient に適用した加法性の比較。
方針：二つの完全関手の像を積へ束ねる。
規約：同値性は別に証明する。使われ方：object と core 実現の加法性の共通の型。 -/
def sTwoAdditivityComparisonNat (F : StableModel.{u} ⥤ SSet.{u}) :
    sEndofunctor 2 ⋙ F ⟶ F ⊗ F where
  app X := CartesianMonoidalCategory.lift (F.map (sTwoSubobject X)) (F.map (sTwoQuotient X))
  naturality {X Y} f := by
    apply CartesianMonoidalCategory.hom_ext
    · change F.map ((sEndofunctor 2).map f) ≫
          CartesianMonoidalCategory.lift (F.map (sTwoSubobject Y))
            (F.map (sTwoQuotient Y)) ≫ fst _ _ =
        CartesianMonoidalCategory.lift (F.map (sTwoSubobject X)) (F.map (sTwoQuotient X)) ≫
          (F.map f ⊗ₘ F.map f) ≫ fst _ _
      simp only [CartesianMonoidalCategory.lift_fst, tensorHom_fst, ← Category.assoc]
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact congrArg F.map ((sTwoFaceComparisonNat 2).naturality f)
    · change F.map ((sEndofunctor 2).map f) ≫
          CartesianMonoidalCategory.lift (F.map (sTwoSubobject Y))
            (F.map (sTwoQuotient Y)) ≫ snd _ _ =
        CartesianMonoidalCategory.lift (F.map (sTwoSubobject X)) (F.map (sTwoQuotient X)) ≫
          (F.map f ⊗ₘ F.map f) ≫ snd _ _
      simp only [CartesianMonoidalCategory.lift_snd, tensorHom_snd, ← Category.assoc]
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact congrArg F.map ((sTwoFaceComparisonNat 0).naturality f)

/-- 概要：加法性の比較の第一射影は subobject の像そのもの。
方針：cartesian tensor への持ち上げの回収式を使う。
規約：全ての空間値関手に共通。使われ方：加法性の型と射の照合。 -/
lemma sTwoAdditivityComparisonNat_fst (F : StableModel.{u} ⥤ SSet.{u}) (X : StableModel.{u}) :
    (sTwoAdditivityComparisonNat F).app X ≫ fst (F.obj X) (F.obj X) =
      F.map (sTwoSubobject X) := CartesianMonoidalCategory.lift_fst _ _

/-- 概要：加法性の比較の第二射影は quotient の像そのもの。
方針：cartesian tensor への持ち上げの回収式を使う。
規約：全ての空間値関手に共通。使われ方：加法性の型と射の照合。 -/
lemma sTwoAdditivityComparisonNat_snd (F : StableModel.{u} ⥤ SSet.{u}) (X : StableModel.{u}) :
    (sTwoAdditivityComparisonNat F).app X ≫ snd (F.obj X) (F.obj X) =
      F.map (sTwoQuotient X) := CartesianMonoidalCategory.lift_snd _ _

/-- 概要：object S 構成の subobject・quotient の加法性の比較射。
方針：共通の比較に object S 関手を代入する。
規約：McCarthy 法で弱同値性を示す対象。使われ方：object 単体集合での加法性。 -/
def objectSAdditivityComparisonNat :
    sEndofunctor.{u} 2 ⋙ objectSConstructionFunctor ⟶
      objectSConstructionFunctor ⊗ objectSConstructionFunctor :=
  sTwoAdditivityComparisonNat objectSConstructionFunctor

/-- 概要：core S• の対角実現での subobject・quotient の加法性の比較射。
方針：共通の比較に一回の core S の実現関手を代入する。
規約：S₂C≃C×C とは主張しない。使われ方：McCarthy 加法性の最終的な実現での射。 -/
def coreSAdditivityComparisonNat :
    sEndofunctor.{u} 2 ⋙ multiRealizationFunctor 1 ⟶
      multiRealizationFunctor 1 ⊗ multiRealizationFunctor 1 :=
  sTwoAdditivityComparisonNat (multiRealizationFunctor 1)

end SerrePositivity.KST.SConstruction
