module
public import SerrePositivity.DifferentialGraded.Resolution.Basic
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionTriangleFamily
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagon

/-! # 指定dg圏解像度上の導来bimodule圏と合成

## 概要
元のunderived積dg圏上の導来bimodule圏との同値は仮定しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t v' w' z' t'
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory
open BimoduleTensor
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w} {E : Type z} {F : Type t}
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]

/-- 指定した解像度のunderived積上で準同型を局所化する。 -/
abbrev DerivedCategory (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :=
  DerivedBimoduleCategory A P.source Q.source

omit [DGCategory A C] [DGCategory A E] [DGCategory A F] in
def diagonal (P : KFlatDGResolution.{u, v, v'} A B) : DerivedCategory A P P :=
  (bimoduleToDerived A P.source P.source).obj (rightKFlatDiagonal A P.source).obj

def composeFunctor (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E) :
    DerivedCategory A Q R ⥤ (DerivedCategory A P Q ⥤ DerivedCategory A P R) :=
  derivedBimoduleComposeFunctor A P.source Q.source R.source R.homKFlat

def rightUnitIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    (composeFunctor A P Q Q).obj (diagonal A Q) ≅ 𝟭 (DerivedCategory A P Q) :=
  derivedBimoduleRightUnitIso A P.source Q.source Q.homKFlat

def leftUnitFunctor (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A P Q ⥤ DerivedCategory A P Q :=
  derivedBimoduleLeftUnitFunctor A P.source Q.source Q.homKFlat

def leftUnitIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    leftUnitFunctor A P Q ≅ 𝟭 (DerivedCategory A P Q) :=
  derivedBimoduleLeftUnitIso A P.source Q.source Q.homKFlat

def associator (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E)
    (S : KFlatDGResolution.{u, t, t'} A F)
    (M : DerivedCategory A Q R) (N : DerivedCategory A R S) :
    (composeFunctor A P Q R).obj M ⋙ (composeFunctor A P R S).obj N ≅
      (composeFunctor A P Q S).obj (((composeFunctor A Q R S).obj N).obj M) :=
  derivedBimoduleAssociator A P.source Q.source R.source S.source R.homKFlat S.homKFlat M N

lemma triangle (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E)
    (M : DerivedCategory A Q R) :
    (associator A P Q Q R (diagonal A Q) M).hom ≫
        (composeFunctor A P Q R).map ((leftUnitIso A Q R).hom.app M) =
      Functor.whiskerRight (rightUnitIso A P Q).hom ((composeFunctor A P Q R).obj M) :=
  derivedBimoduleTriangle_app A P.source Q.source R.source Q.homKFlat R.homKFlat M

/-- 恒等解像度では既存の主導来合成と定義通り一致する。 -/
lemma composeFunctor_refl [Small.{u} B] [Small.{u} C] [Small.{u} E]
    (hB : localHomKFlat A B) (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    composeFunctor A (KFlatDGResolution.refl A B hB) (KFlatDGResolution.refl A C hC)
        (KFlatDGResolution.refl A E hE) =
      derivedBimoduleComposeFunctor A B C E hE := rfl

end SerrePositivity.DifferentialGraded.ResolutionBimodule
