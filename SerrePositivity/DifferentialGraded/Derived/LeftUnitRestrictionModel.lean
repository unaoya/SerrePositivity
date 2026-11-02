module
public import SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparison
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionLeftUnitComputation

/-! # 制限後の任意K-flat解像度で計算する左単位square

## 概要
制限後の任意K-flat解像度で計算する左単位square。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C)

local notation "RP" => Functor.obj
  (BimoduleCategory.middleRightRestrictionFunctor A B D C F) P
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F)
  (BimoduleCategory.of A B B (Bimodule.diagonal A B))
local notation "DD" => BimoduleCategory.of A D D (Bimodule.diagonal A D)
local notation "qD" => Bimodule.diagonalRestrictionMap A D B F

omit [Small.{u} C] in
/-- 指定増大射付き左単位squareを、既存の導来局所化に送る。 -/
lemma leftUnitRestriction_localized_augmentation (R : BimoduleCategory A D C) (q : R ⟶ RP) :
    (bimoduleToDerived A D C).map (composeMap A D D C qD (𝟙 R)) ≫
      (bimoduleToDerived A D C).map (composeRightRestrictionIso A B D D C F LD R).hom ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (middleRestrictionResolvedMap A B B D C F
            (BimoduleCategory.of A B B (Bimodule.diagonal A B)) P R q)) ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom) =
    (bimoduleToDerived A D C).map
        (leftBimoduleUnitIso A D C (BimoduleCategory.underlying A D C R)).hom ≫
      (bimoduleToDerived A D C).map q := by
  have h := congrArg ((bimoduleToDerived A D C).map)
    (leftUnitRestriction_augmentation A B D C F P R q)
  simpa only [middleRestrictionResolvedMap, BimoduleCategory.middleLeftRestrictionFunctor,
    BimoduleCategory.underlying, BimoduleCategory.of,
    CategoryTheory.Functor.map_comp, Category.assoc] using h

/-- 任意の指定K-flat解像度による計算経路は、既存の導来左単位子そのもの。 -/
lemma derivedLeftUnitRestriction_resolution (hC : localHomKFlat A C)
    (R : RightKFlatBimoduleCategory A D C) (q : R.obj ⟶ RP)
    (hq : BimoduleCategory.quasiIso A D C q) :
    (derivedBimoduleComposeResolutionComputation A D D C hC RP R q hq).hom.app
        ((bimoduleToDerived A D D).obj DD) ≫
      (bimoduleToDerived A D C).map (composeMap A D D C qD (𝟙 R.obj)) ≫
      (bimoduleToDerived A D C).map (composeRightRestrictionIso A B D D C F LD R.obj).hom ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (middleRestrictionResolvedMap A B B D C F
            (BimoduleCategory.of A B B (Bimodule.diagonal A B)) P R.obj q)) ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom) =
    (derivedBimoduleLeftUnitIso A D C hC).hom.app ((bimoduleToDerived A D C).obj RP) := by
  rw [leftUnitRestriction_localized_augmentation A B D C F P R.obj q,
    derivedBimoduleLeftUnitIso_resolution_app A D C hC RP R q hq]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
