module

public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.DifferentialGraded.Resolution.FixedObject
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionEvaluation
public import SerrePositivity.DifferentialGraded.Derived.FunctorDerivedEquivalence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionEquivalence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSimultaneousRestriction
public import SerrePositivity.DifferentialGraded.Derived.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullComposition

/-!
# Resolution.Composition

## 概要
8 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w v' w' z' t' z v'' w'' z'' t

/-! ## CanonicalZigzag（旧 SerrePositivity/DifferentialGraded/Resolution/CanonicalZigzag.lean） -/

/-! # 任意の指定K-flat解像度と標準解像度の準同値zigzag

## 概要
P.source ← 標準解像度(P.source) → 標準解像度(D) はDへの増大と可換する。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CanonicalZigzag

noncomputable section
namespace SerrePositivity.DifferentialGraded.KFlatDGResolution
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  (P : KFlatDGResolution.{u, v, w} A D)

abbrev ComparisonSource : Type w := DGCategoryCellResolution.Source A P.source

def comparisonLeft : DGFunctor A P.ComparisonSource P.source :=
  DGCategoryCellResolution.augmentation A P.source

def comparisonRight : DGFunctor A P.ComparisonSource (canonical A D).source :=
  DGCategoryCellResolution.comparisonFunctor A P.source D P.augmentation

omit [Small.{u} D] in
lemma comparisonLeft_quasiEquivalence : QuasiEquivalence P.comparisonLeft :=
  DGCategoryCellResolution.augmentation_quasiEquivalence A P.source

lemma comparisonRight_quasiEquivalence : QuasiEquivalence P.comparisonRight :=
  DGCategoryCellResolution.comparisonFunctor_quasiEquivalence A P.source D P.augmentation
    P.quasiEquivalence

omit [Small.{u} D] in
lemma comparisonSource_homKFlat : localHomKFlat A P.ComparisonSource :=
  DGCategoryCellResolution.source_homKFlat A P.source

/-- zigzagの両脚はDへの増大と厳密に可換する。 -/
lemma comparison_augmentation :
    P.comparisonRight.comp (canonical A D).augmentation = P.comparisonLeft.comp P.augmentation :=
  DGCategoryCellResolution.comparisonFunctor_augmentation A P.source D P.augmentation

end SerrePositivity.DifferentialGraded.KFlatDGResolution
end

end CanonicalZigzag

/-! ## Restriction（旧 SerrePositivity/DifferentialGraded/Resolution/Restriction.lean） -/

/-! # 解像度比較に沿う導来bimodule制限の実際の関手

## 概要
準同値zigzagの両脚から比較関手を得る。これらの同値性と合成比較は別の受入条件である。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Restriction

noncomputable section
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory
variable (A : Type u) [CommRing A] {B : Type v} [DGCategory A B]
  {C : Type w} [DGCategory A C]

/-- 任意の解像度source間のdg関手に沿う導来bimodule制限。 -/
def restriction (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C)
    (R : KFlatDGResolution.{u, v, z'} A B) (S : KFlatDGResolution.{u, w, t'} A C)
    (f : DGFunctor A R.source P.source) (g : DGFunctor A S.source Q.source) :
    DerivedCategory A P Q ⥤ DerivedCategory A R S :=
  derivedBimoduleRestriction A R.source S.source P.source Q.source f g

/-- 任意解像度から標準解像度比較の中間sourceへ制限する。 -/
def comparisonLeft (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A P Q ⥤ DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  derivedBimoduleRestriction A P.ComparisonSource Q.ComparisonSource P.source Q.source
    P.comparisonLeft Q.comparisonLeft

variable [Small.{u} B] [Small.{u} C]

/-- 元のdg圏の局所K-flat性を要求せず、標準解像度側から同じ中間圏へ制限する。 -/
def comparisonRight (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C) ⥤
      DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  derivedBimoduleRestriction A P.ComparisonSource Q.ComparisonSource
    (KFlatDGResolution.canonical A B).source (KFlatDGResolution.canonical A C).source
    P.comparisonRight Q.comparisonRight

end SerrePositivity.DifferentialGraded.ResolutionBimodule
end

end Restriction

/-! ## DerivedEquivalence（旧 SerrePositivity/DifferentialGraded/Resolution/DerivedEquivalence.lean） -/

/-! # dg圏解像度の増大・比較に沿う主導来加群圏の同値

## 概要
dg圏解像度の増大・比較に沿う主導来加群圏の同値。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section DerivedEquivalence

noncomputable section
namespace SerrePositivity.DifferentialGraded.KFlatDGResolution
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  (P : KFlatDGResolution.{u, v, w} A D)

/-- 元のdg圏のHomにflatnessを要求せず、増大に沿って実際の導来加群圏を比較する。 -/
def moduleDerivedEquivalence : DerivedModuleCategory A P.source ≌ DerivedModuleCategory A D :=
  dgFunctorDerivedEquivalence A P.source D P.augmentation P.quasiEquivalence

omit [Small.{u} D] in
/-- 標準zigzagの左脚に沿う実際の導来同値。 -/
def comparisonLeftModuleDerivedEquivalence :
    DerivedModuleCategory A P.ComparisonSource ≌ DerivedModuleCategory A P.source :=
  dgFunctorDerivedEquivalence A P.ComparisonSource P.source P.comparisonLeft
    P.comparisonLeft_quasiEquivalence

/-- 標準zigzagの右脚に沿う実際の導来同値。 -/
def comparisonRightModuleDerivedEquivalence :
    DerivedModuleCategory A P.ComparisonSource ≌
      DerivedModuleCategory A (canonical A D).source :=
  dgFunctorDerivedEquivalence A P.ComparisonSource (canonical A D).source P.comparisonRight
    P.comparisonRight_quasiEquivalence

/-- 二つの指定解像度の主導来加群圏を、元のdg圏を経由して比較する。 -/
def changeModuleDerivedEquivalence (Q : KFlatDGResolution.{u, v, z} A D) :
    DerivedModuleCategory A P.source ≌ DerivedModuleCategory A Q.source :=
  P.moduleDerivedEquivalence.trans Q.moduleDerivedEquivalence.symm

lemma changeModuleDerivedEquivalence_functor (Q : KFlatDGResolution.{u, v, z} A D) :
    (P.changeModuleDerivedEquivalence Q).functor =
      dgDerivedExtension A P.source D P.augmentation ⋙
        dgDerivedRestriction A Q.source D Q.augmentation := rfl

lemma changeModuleDerivedEquivalence_inverse (Q : KFlatDGResolution.{u, v, z} A D) :
    (P.changeModuleDerivedEquivalence Q).inverse =
      dgDerivedExtension A Q.source D Q.augmentation ⋙
        dgDerivedRestriction A P.source D P.augmentation := rfl

end SerrePositivity.DifferentialGraded.KFlatDGResolution
end

end DerivedEquivalence

/-! ## BimoduleDerivedEquivalence（旧 SerrePositivity/DifferentialGraded/Resolution/BimoduleDerivedEquivalence.lean） -/

/-! # 指定解像度の導来bimodule圏を標準zigzagで比較する同値

## 概要
指定解像度の導来bimodule圏を標準zigzagで比較する同値。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleDerivedEquivalence

noncomputable section
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory
variable (A : Type u) [CommRing A] {B : Type v} [DGCategory A B]
  {C : Type w} [DGCategory A C]

/-- 比較zigzagの左脚の、既存の導来制限を順方向とする同値。 -/
def comparisonLeftEquivalence (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A P Q ≌ DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  derivedBimoduleRestrictionEquivalence A P.ComparisonSource Q.ComparisonSource P.source Q.source
    P.comparisonLeft Q.comparisonLeft P.comparisonLeft_quasiEquivalence
    Q.comparisonLeft_quasiEquivalence Q.comparisonSource_homKFlat P.homKFlat

lemma comparisonLeftEquivalence_functor (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    (comparisonLeftEquivalence A P Q).functor = comparisonLeft A P Q := rfl

variable [Small.{u} B] [Small.{u} C]

/-- 比較zigzagの右脚の、標準解像度側からの既存導来制限を順方向とする同値。 -/
def comparisonRightEquivalence (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C) ≌
      DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  derivedBimoduleRestrictionEquivalence A P.ComparisonSource Q.ComparisonSource
    (KFlatDGResolution.canonical A B).source (KFlatDGResolution.canonical A C).source
    P.comparisonRight Q.comparisonRight P.comparisonRight_quasiEquivalence
    Q.comparisonRight_quasiEquivalence Q.comparisonSource_homKFlat
    (KFlatDGResolution.canonical A B).homKFlat

lemma comparisonRightEquivalence_functor (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    (comparisonRightEquivalence A P Q).functor = comparisonRight A P Q := rfl

/-- 任意の指定解像度の導来bimodule圏から標準解像度の導来bimodule圏への比較。 -/
def canonicalComparisonEquivalence (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A P Q ≌
      DerivedCategory A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C) :=
  (comparisonLeftEquivalence A P Q).trans (comparisonRightEquivalence A P Q).symm

/-- 両側の指定解像度を同時に変更する、実際の導来bimodule圏の同値。 -/
def changeEquivalence (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, v, z'} A B)
    (S : KFlatDGResolution.{u, w, t'} A C) : DerivedCategory A P Q ≌ DerivedCategory A R S :=
  (canonicalComparisonEquivalence A P Q).trans (canonicalComparisonEquivalence A R S).symm

end SerrePositivity.DifferentialGraded.ResolutionBimodule
end

end BimoduleDerivedEquivalence

/-! ## CompositionComparison（旧 SerrePositivity/DifferentialGraded/Resolution/CompositionComparison.lean） -/

/-! # 共通dg圏解像度への既存の両端制限と導来bimodule合成の比較

## 概要
共通dg圏解像度への既存の両端制限と導来bimodule合成の比較。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompositionComparison

noncomputable section
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  {B : Type v} [DGCategory A B] {C : Type w} [DGCategory A C]
  {E : Type z} [DGCategory A E]

/-- 指定解像度から共通比較sourceへの三つの既存制限は、導来合成と自然に可換する。 -/
def comparisonLeftComposeIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E) :
    comparisonLeft A Q R ⋙
        derivedBimoduleComposeFunctor A P.ComparisonSource Q.ComparisonSource R.ComparisonSource
          R.comparisonSource_homKFlat ⋙
        (whiskeringLeft _ _ _).obj (comparisonLeft A P Q) ≅
      composeFunctor A P Q R ⋙ (whiskeringRight _ _ _).obj (comparisonLeft A P R) :=
  derivedBimoduleComposeRestrictionIso A P.source P.ComparisonSource Q.source Q.ComparisonSource
    R.source R.ComparisonSource P.comparisonLeft Q.comparisonLeft R.comparisonLeft
    R.homKFlat R.comparisonSource_homKFlat Q.comparisonLeft_quasiEquivalence

variable [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 標準解像度から同じ共通比較sourceへの三つの既存制限も、導来合成と自然に可換する。 -/
def comparisonRightComposeIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E) :
    comparisonRight A Q R ⋙
        derivedBimoduleComposeFunctor A P.ComparisonSource Q.ComparisonSource R.ComparisonSource
          R.comparisonSource_homKFlat ⋙
        (whiskeringLeft _ _ _).obj (comparisonRight A P Q) ≅
      composeFunctor A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C)
          (KFlatDGResolution.canonical A E) ⋙
        (whiskeringRight _ _ _).obj (comparisonRight A P R) :=
  derivedBimoduleComposeRestrictionIso A
    (KFlatDGResolution.canonical A B).source P.ComparisonSource
    (KFlatDGResolution.canonical A C).source Q.ComparisonSource
    (KFlatDGResolution.canonical A E).source R.ComparisonSource
    P.comparisonRight Q.comparisonRight R.comparisonRight
    (KFlatDGResolution.canonical A E).homKFlat R.comparisonSource_homKFlat
    Q.comparisonRight_quasiEquivalence

end SerrePositivity.DifferentialGraded.ResolutionBimodule
end

end CompositionComparison

/-! ## CompositionChange（旧 SerrePositivity/DifferentialGraded/Resolution/CompositionChange.lean） -/

/-! # 指定dg圏解像度の変更同値と導来bimodule合成

## 概要
指定dg圏解像度の変更同値と導来bimodule合成。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompositionChange

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory CategoryTheory.Functor BimoduleTensor

/-- 三つの圏同値に沿う合成比較を、単位・余単位により逆向きの合成比較へ送る。 -/
def inverseCompositionComparison
    {C₁ : Type*} {C₂ : Type*} {C₃ : Type*} {D₁ : Type*} {D₂ : Type*} {D₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₁] [Category* D₂] [Category* D₃]
    (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) (E₃ : C₃ ≌ D₃)
    (H₁ : C₂ ⥤ C₁ ⥤ C₃) (H₂ : D₂ ⥤ D₁ ⥤ D₃)
    (e : E₂.functor ⋙ H₂ ⋙ (whiskeringLeft _ _ _).obj E₁.functor ≅
      H₁ ⋙ (whiskeringRight _ _ _).obj E₃.functor) :
    E₂.inverse ⋙ H₁ ⋙ (whiskeringLeft _ _ _).obj E₁.inverse ≅
      H₂ ⋙ (whiskeringRight _ _ _).obj E₃.inverse :=
  Functor.isoWhiskerLeft
      (E₂.inverse ⋙ H₁ ⋙ (whiskeringLeft _ _ _).obj E₁.inverse)
      ((whiskeringRight _ _ _).mapIso E₃.unitIso) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft E₂.inverse e.symm)
        ((whiskeringLeft _ _ _).obj E₁.inverse))
      ((whiskeringRight _ _ _).obj E₃.inverse) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (E₂.inverse ⋙ E₂.functor ⋙ H₂)
        ((whiskeringLeft _ _ _).mapIso E₁.counitIso))
      ((whiskeringRight _ _ _).obj E₃.inverse) ≪≫
    Functor.isoWhiskerRight E₂.counitIso
      (H₂ ⋙ (whiskeringRight _ _ _).obj E₃.inverse) ≪≫
    Functor.leftUnitor _

variable (A : Type u) [CommRing A]
  {B : Type v} [DGCategory A B] [Small.{u} B]
  {C : Type w} [DGCategory A C] [Small.{u} C]
  {E : Type z} [DGCategory A E] [Small.{u} E]

/-- 共通比較sourceを通る既存の標準解像度比較同値は、導来合成を自然同型で保つ。 -/
def canonicalComparisonComposeIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E) :
    (canonicalComparisonEquivalence A Q R).functor ⋙
        composeFunctor A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C)
          (KFlatDGResolution.canonical A E) ⋙
        (whiskeringLeft _ _ _).obj (canonicalComparisonEquivalence A P Q).functor ≅
      composeFunctor A P Q R ⋙
        (whiskeringRight _ _ _).obj (canonicalComparisonEquivalence A P R).functor :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (comparisonLeft A Q R)
        (inverseCompositionComparison
          (comparisonRightEquivalence A P Q) (comparisonRightEquivalence A Q R)
          (comparisonRightEquivalence A P R)
          (composeFunctor A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C)
            (KFlatDGResolution.canonical A E))
          (derivedBimoduleComposeFunctor A P.ComparisonSource Q.ComparisonSource R.ComparisonSource
            R.comparisonSource_homKFlat) (comparisonRightComposeIso A P Q R)))
      ((whiskeringLeft _ _ _).obj (comparisonLeft A P Q)) ≪≫
    Functor.isoWhiskerRight (comparisonLeftComposeIso A P Q R)
      ((whiskeringRight _ _ _).obj (comparisonRightEquivalence A P R).inverse)

/-- 両端の指定解像度を同時に変える既存のchangeEquivalenceは、導来合成を自然同型で保つ。 -/
def changeComposeIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E)
    (P' : KFlatDGResolution.{u, v, v''} A B) (Q' : KFlatDGResolution.{u, w, w''} A C)
    (R' : KFlatDGResolution.{u, z, z''} A E) :
    (changeEquivalence A Q R Q' R').functor ⋙ composeFunctor A P' Q' R' ⋙
        (whiskeringLeft _ _ _).obj (changeEquivalence A P Q P' Q').functor ≅
      composeFunctor A P Q R ⋙
        (whiskeringRight _ _ _).obj (changeEquivalence A P R P' R').functor :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (canonicalComparisonEquivalence A Q R).functor
        (inverseCompositionComparison
          (canonicalComparisonEquivalence A P' Q') (canonicalComparisonEquivalence A Q' R')
          (canonicalComparisonEquivalence A P' R') (composeFunctor A P' Q' R')
          (composeFunctor A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C)
            (KFlatDGResolution.canonical A E)) (canonicalComparisonComposeIso A P' Q' R')))
      ((whiskeringLeft _ _ _).obj (canonicalComparisonEquivalence A P Q).functor) ≪≫
    Functor.isoWhiskerRight (canonicalComparisonComposeIso A P Q R)
      ((whiskeringRight _ _ _).obj (canonicalComparisonEquivalence A P' R').inverse)

end SerrePositivity.DifferentialGraded.ResolutionBimodule
end

end CompositionChange

/-! ## DiagonalComparison（旧 SerrePositivity/DifferentialGraded/Resolution/DiagonalComparison.lean） -/

/-! # 指定dg圏解像度の既存の変更同値による対角bimoduleの保存

## 概要
指定dg圏解像度の既存の変更同値による対角bimoduleの保存。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section DiagonalComparison

noncomputable section
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 共通比較sourceの対角を、既存の導来bimodule圏の対象として読む。 -/
def comparisonDiagonal (P : KFlatDGResolution.{u, v, w} A D) :
    DerivedBimoduleCategory A P.ComparisonSource P.ComparisonSource :=
  (bimoduleToDerived A P.ComparisonSource P.ComparisonSource).obj
    (rightKFlatDiagonal A P.ComparisonSource).obj

/-- 指定解像度から共通sourceへの既存の比較左脚は、対角を同型で保存する。 -/
def comparisonLeftDiagonalIso (P : KFlatDGResolution.{u, v, w} A D) :
    (comparisonLeft A P P).obj (diagonal A P) ≅ comparisonDiagonal A P :=
  (derivedDiagonalRestrictionIso A P.ComparisonSource P.source P.comparisonLeft
    P.comparisonLeft_quasiEquivalence.1).symm

variable [Small.{u} D]

/-- 標準解像度から共通sourceへの既存の比較右脚も、対角を同型で保存する。 -/
def comparisonRightDiagonalIso (P : KFlatDGResolution.{u, v, w} A D) :
    (comparisonRight A P P).obj (diagonal A (KFlatDGResolution.canonical A D)) ≅
      comparisonDiagonal A P :=
  (derivedDiagonalRestrictionIso A P.ComparisonSource (KFlatDGResolution.canonical A D).source
    P.comparisonRight P.comparisonRight_quasiEquivalence.1).symm

/-- 既存の標準解像度比較同値は、指定対角を標準対角へ送る。 -/
def canonicalComparisonDiagonalIso (P : KFlatDGResolution.{u, v, w} A D) :
    (canonicalComparisonEquivalence A P P).functor.obj (diagonal A P) ≅
      diagonal A (KFlatDGResolution.canonical A D) :=
  (comparisonRightEquivalence A P P).inverse.mapIso
      (comparisonLeftDiagonalIso A P ≪≫ (comparisonRightDiagonalIso A P).symm) ≪≫
    ((comparisonRightEquivalence A P P).unitIso.app
      (diagonal A (KFlatDGResolution.canonical A D))).symm

/-- 両端の指定解像度を同時に変更する既存の同値は、対角bimoduleを保存する。 -/
def changeDiagonalIso (P : KFlatDGResolution.{u, v, w} A D)
    (Q : KFlatDGResolution.{u, v, z} A D) :
    (changeEquivalence A P P Q Q).functor.obj (diagonal A P) ≅ diagonal A Q :=
  (canonicalComparisonEquivalence A Q Q).inverse.mapIso
      (canonicalComparisonDiagonalIso A P ≪≫ (canonicalComparisonDiagonalIso A Q).symm) ≪≫
    ((canonicalComparisonEquivalence A Q Q).unitIso.app (diagonal A Q)).symm

end SerrePositivity.DifferentialGraded.ResolutionBimodule
end

end DiagonalComparison

/-! ## MiddleCompositionComparison（旧 SerrePositivity/DifferentialGraded/Resolution/MiddleCompositionComparison.lean） -/

/-! # dg圏解像度比較の両脚に沿う全導来bimodule合成比較

## 概要
dg圏解像度比較の両脚に沿う全導来bimodule合成比較。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleCompositionComparison

noncomputable section
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  {C : Type w} [DGCategory A C]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

/-- 指定解像度側から共通比較sourceへ中間圏を制限した合成の比較。 -/
def middleComparisonLeftIso (P : KFlatDGResolution.{u, w, w'} A C) :
    middleRestrictionDerivedSource A B P.source P.ComparisonSource L P.comparisonLeft hL ≅
      derivedBimoduleComposeFunctor A B P.source L hL :=
  derivedMiddleRestrictionIso A B P.source P.ComparisonSource L P.comparisonLeft
    P.comparisonLeft_quasiEquivalence hL

/-- 共通sourceをさらに準同値で細分しても、既存の一段階比較と二段階比較が一致する。 -/
lemma middleComparisonLeftIso_refine (P : KFlatDGResolution.{u, w, w'} A C)
    (S : Type t) [DGCategory A S] [Small.{u} S]
    (H : DGFunctor A S P.ComparisonSource) (hH : QuasiEquivalence H) :
    middleIteratedDerivedSourceIso A B S P.ComparisonSource P.source L H P.comparisonLeft hL ≪≫
        derivedMiddleRestrictionIso A B P.source S L (H.comp P.comparisonLeft)
          (quasiEquivalence_comp H P.comparisonLeft hH P.comparisonLeft_quasiEquivalence) hL =
      middleIteratedDerivedIso A B S P.ComparisonSource P.source L H P.comparisonLeft hL
        hH P.comparisonLeft_quasiEquivalence :=
  derivedMiddleRestrictionIso_functor_comp A B S P.ComparisonSource P.source L
    H P.comparisonLeft hL hH P.comparisonLeft_quasiEquivalence

variable [Small.{u} C]

/-- 標準解像度側から同じ共通sourceへ中間圏を制限した合成の比較。 -/
def middleComparisonRightIso (P : KFlatDGResolution.{u, w, w'} A C) :
    middleRestrictionDerivedSource A B (KFlatDGResolution.canonical A C).source
        P.ComparisonSource L P.comparisonRight hL ≅
      derivedBimoduleComposeFunctor A B (KFlatDGResolution.canonical A C).source L hL :=
  derivedMiddleRestrictionIso A B (KFlatDGResolution.canonical A C).source
    P.ComparisonSource L P.comparisonRight P.comparisonRight_quasiEquivalence hL

lemma middleComparisonRightIso_refine (P : KFlatDGResolution.{u, w, w'} A C)
    (S : Type t) [DGCategory A S] [Small.{u} S]
    (H : DGFunctor A S P.ComparisonSource) (hH : QuasiEquivalence H) :
    middleIteratedDerivedSourceIso A B S P.ComparisonSource
        (KFlatDGResolution.canonical A C).source L H P.comparisonRight hL ≪≫
        derivedMiddleRestrictionIso A B (KFlatDGResolution.canonical A C).source S L
          (H.comp P.comparisonRight)
          (quasiEquivalence_comp H P.comparisonRight hH P.comparisonRight_quasiEquivalence) hL =
      middleIteratedDerivedIso A B S P.ComparisonSource
        (KFlatDGResolution.canonical A C).source L H P.comparisonRight hL
        hH P.comparisonRight_quasiEquivalence :=
  derivedMiddleRestrictionIso_functor_comp A B S P.ComparisonSource
    (KFlatDGResolution.canonical A C).source L H P.comparisonRight hL
    hH P.comparisonRight_quasiEquivalence

end SerrePositivity.DifferentialGraded.ResolutionBimodule
end

end MiddleCompositionComparison
