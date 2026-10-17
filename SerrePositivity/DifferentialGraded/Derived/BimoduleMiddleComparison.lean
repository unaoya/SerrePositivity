module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleMap
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionResolution

/-! # 中間圏の制限後に解像度を取る導来bimodule合成比較

## 概要
制限後のK-flat性を仮定せず、制限後に選んだ解像度の増大を通して比較射を構成する。
準同値の場合の可逆性・解像度独立性は後続の受入条件である。

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
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)

/-- 制限後の解像度の増大と、全Hom自然な中間圏比較射の合成。 -/
def middleRestrictionResolvedMap (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    (R : BimoduleCategory A D E)
    (q : R ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q))) :
    BimoduleCategory.of A B E (compose A B D E
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))
      (BimoduleCategory.underlying A D E R)) ⟶
        BimoduleCategory.of A B E (compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q)) :=
  composeMap A B D E (𝟙 (BimoduleCategory.of A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) q ≫
    middleRestrictionComparisonMap A B C D E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q)

omit [Small.{u} E] in
/-- 厳密な増大squareに関する解像度計算射の整合性。 -/
lemma middleRestrictionResolvedMap_comp (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    {R S : BimoduleCategory A D E}
    (r : S ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q))) (g : R ⟶ S) :
    composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) g ≫
      middleRestrictionResolvedMap A B C D E F P Q S r =
        middleRestrictionResolvedMap A B C D E F P Q R (g ≫ r) := by
  dsimp only [middleRestrictionResolvedMap]
  rw [← Category.assoc, ← composeMap_comp, Category.id_comp]

/-- 既存の導来合成を、制限後に選んだ右K-flat解像度で計算する同型。 -/
def middleRestrictionSourceComputation (hE : localHomKFlat A E)
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q)))
    (hq : BimoduleCategory.quasiIso A D E q) :
    ((derivedBimoduleComposeFunctor A B D E hE).obj
      ((bimoduleToDerived A D E).obj (BimoduleCategory.of A D E
        (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q))))).obj
      ((bimoduleToDerived A B D).obj (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) ≅
      (bimoduleToDerived A B E).obj (BimoduleCategory.of A B E (compose A B D E
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))
        (BimoduleCategory.underlying A D E R.obj))) :=
  (derivedBimoduleComposeResolutionComputation A B D E hE _ R q hq).app _ ≪≫
    derivedComposeWithComputation A B D E R.obj R.property _

/-- 後因子のK-flatモデルと制限後の解像度を指定した、実際の導来合成間の比較射。 -/
def derivedMiddleRestrictionComparison (hE : localHomKFlat A E)
    (P : BimoduleCategory A B C) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q.obj)))
    (hq : BimoduleCategory.quasiIso A D E q) :
    ((derivedBimoduleComposeFunctor A B D E hE).obj
      ((bimoduleToDerived A D E).obj (BimoduleCategory.of A D E
        (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q.obj))))).obj
      ((bimoduleToDerived A B D).obj (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) ⟶
      ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj Q.obj)).obj ((bimoduleToDerived A B C).obj P) :=
  (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).inv

/-- 制限後の既存の標準semifree解像度を使う比較。追加のK-flat仮定は不要。 -/
def derivedMiddleRestrictionCanonicalComparison (hE : localHomKFlat A E)
    (P : BimoduleCategory A B C) (Q : RightKFlatBimoduleCategory A C E) :
    ((derivedBimoduleComposeFunctor A B D E hE).obj
      ((bimoduleToDerived A D E).obj (BimoduleCategory.of A D E
        (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q.obj))))).obj
      ((bimoduleToDerived A B D).obj (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) ⟶
      ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj Q.obj)).obj ((bimoduleToDerived A B C).obj P) :=
  derivedMiddleRestrictionComparison A B C D E F hE P Q
    (rightKFlatResolutionObj A D E hE _)
    (bimoduleCanonicalSemifreeResolution A D E _).π
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
