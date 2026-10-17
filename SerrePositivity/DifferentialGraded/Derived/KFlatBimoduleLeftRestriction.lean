module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleLocalization
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps

/-! # 外側の左dg作用を制限しても右相対K-flat性を保つ

## 概要
外側の左dg作用を制限しても右相対K-flat性を保つ。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] (D : Type z) [DGCategory A D] (F : DGFunctor A D E)

/-- 外側の左作用の制限は、各右加群を再選択するので右相対K-flat性を保つ。 -/
lemma leftRestriction_rightRelativeKFlat (Q : Bimodule A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E Q) :
    Bimodule.rightRelativeKFlat A C D (Bimodule.leftRestriction A C E D F Q) :=
  fun d => hQ (F.obj d)

lemma leftRestriction_quasiIso {Q Q' : BimoduleCategory A C E} (q : Q ⟶ Q')
    (hq : BimoduleCategory.quasiIso A C E q) :
    BimoduleCategory.quasiIso A C D
      ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map q) :=
  fun c d => hq c (F.obj d)

/-- 右K-flat部分圏上の、外側の左作用の実際の制限関手。 -/
def rightKFlatLeftRestriction :
    RightKFlatBimoduleCategory A C E ⥤ RightKFlatBimoduleCategory A C D where
  obj Q := ⟨(BimoduleCategory.middleLeftRestrictionFunctor A C E D F).obj Q.obj,
    leftRestriction_rightRelativeKFlat A C E D F _ Q.property⟩
  map q := ⟨(BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map q.hom⟩
  map_id Q := by apply ObjectProperty.hom_ext; rfl
  map_comp q r := by apply ObjectProperty.hom_ext; rfl

lemma rightKFlatLeftRestriction_fac :
    rightKFlatLeftRestriction A C E D F ⋙ rightKFlatInclusion A C D =
      rightKFlatInclusion A C E ⋙ BimoduleCategory.middleLeftRestrictionFunctor A C E D F := rfl

lemma rightKFlatLeftRestriction_quasiIso
    {Q Q' : RightKFlatBimoduleCategory A C E} (q : Q ⟶ Q') (hq : rightKFlatQuasiIso A C E q) :
    rightKFlatQuasiIso A C D ((rightKFlatLeftRestriction A C E D F).map q) :=
  leftRestriction_quasiIso A C E D F q.hom hq

end SerrePositivity.DifferentialGraded.BimoduleTensor
