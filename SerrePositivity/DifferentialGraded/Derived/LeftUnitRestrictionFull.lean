module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleOutputRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSourceFull
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFull
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionLeftUnitComputation
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction

/-! # 対角・外側右・中間比較を続ける全導来左単位経路

## 概要
対角・外側右・中間比較を続ける全導来左単位経路。

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
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)

local notation "DB" => BimoduleCategory.of A B B (Bimodule.diagonal A B)
local notation "DD" => BimoduleCategory.of A D D (Bimodule.diagonal A D)
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F) DB
local notation "RR" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)

/-- 直接の対角比較を、外側右制限の既存導来表示へ送る。 -/
def leftUnitRestrictionDerivedDiagonalMap :
    (bimoduleToDerived A D D).obj DD ⟶
      (derivedBimoduleRestriction A D D B D F (DGFunctor.id D)).obj
        ((bimoduleToDerived A B D).obj LD) :=
  (bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D B F) ≫
    (middleRightRestrictionDerivedIso A B D F D).hom.app LD

/-- 既存の全導来中間比較・外側右制限比較・左単位子を続けた自然変換。 -/
def leftUnitRestrictionDerivedComparison (hC : localHomKFlat A C) :
    RR ⋙ derivedBimoduleLeftUnitFunctor A D C hC ⟶ RR :=
  whiskerLeft (RR ⋙ derivedBimoduleComposeFunctor A D D C hC)
      ((CategoryTheory.evaluation _ _).map (leftUnitRestrictionDerivedDiagonalMap A B D F)) ≫
    whiskerRight
      (whiskerLeft RR (derivedBimoduleComposeRightRestrictionIso A B D D C F hC).hom)
      ((CategoryTheory.evaluation _ _).obj ((bimoduleToDerived A B D).obj LD)) ≫
    whiskerLeft (RR ⋙ derivedBimoduleComposeFunctor A B D C hC ⋙
        (whiskeringRight _ _ _).obj RR)
      ((CategoryTheory.evaluation _ _).map
        ((middleLeftRestrictionDerivedIso A B B D F).hom.app DB)) ≫
    whiskerRight
      (whiskerRight (derivedMiddleRestrictionNatTrans A B B D C F hC)
        ((CategoryTheory.evaluation _ _).obj ((bimoduleToDerived A B B).obj DB))) RR ≫
    whiskerRight (derivedBimoduleLeftUnitIso A B C hC).hom RR

/-- 左単位経路の各成分は、既存比較の実際の成分を順に続けた射である。 -/
lemma leftUnitRestrictionDerivedComparison_app (hC : localHomKFlat A C)
    (Q : DerivedBimoduleCategory A B C) :
    (leftUnitRestrictionDerivedComparison A B D C F hC).app Q =
      ((derivedBimoduleComposeFunctor A D D C hC).obj ((RR).obj Q)).map
        (leftUnitRestrictionDerivedDiagonalMap A B D F) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B D D C F hC).hom.app ((RR).obj Q)).app
        ((bimoduleToDerived A B D).obj LD) ≫
      (RR).map (((derivedBimoduleComposeFunctor A B D C hC).obj ((RR).obj Q)).map
        ((middleLeftRestrictionDerivedIso A B B D F).hom.app DB)) ≫
      (RR).map (((derivedMiddleRestrictionNatTrans A B B D C F hC).app Q).app
        ((bimoduleToDerived A B B).obj DB)) ≫
      (RR).map ((derivedBimoduleLeftUnitIso A B C hC).hom.app Q) := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
