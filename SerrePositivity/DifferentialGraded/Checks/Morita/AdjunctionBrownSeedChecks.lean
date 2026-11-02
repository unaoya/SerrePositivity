module
public import SerrePositivity.DifferentialGraded.Morita.Perfect

/-! # 生成元からの初期被覆と局所小性の宇宙監査

## 概要
関手の指定余積保存だけから初期被覆が生成元の全射を表すことを検査する。

## 方針
独立宇宙と恒等関手の例を検査し、添字のsmall性を含む全公開宣言を監査する。

## 規約と注意
随伴・表現可能性・kernel作用の余積保存を仮定済みとはしない。

## 使われ方
U16aの一般右随伴を引用なしに構成する初期段階の再現入口。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

example (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (Y : DerivedModuleCategory A E) : Small.{u} (brownSeedRawIndex A D E L Y) :=
  brownSeedRawIndexSmall A D E L Y

example (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (Y : DerivedModuleCategory A E)
    [PreservesColimit (Discrete.functor (brownSeedFamily A D E L Y)) L]
    (p : D × ℤ) (f : L.obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶ brownSeed A D E L Y,
      L.map g ≫ brownSeedMap A D E L Y = f :=
  brownSeedMap_generator_surjective A D E L Y p f

example (Y : DerivedModuleCategory A D) (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶ brownSeed A D D (𝟭 _) Y,
      g ≫ brownSeedMap A D D (𝟭 _) Y = f :=
  brownSeedMap_generator_surjective A D D (𝟭 _) Y p f

#print axioms brownSeedRawIndex
#print axioms brownSeedRawIndexSmall
#print axioms brownSeedIndex
#print axioms brownSeedFamily
#print axioms brownSeedArrow
#print axioms brownSeed
#print axioms brownSeedMap
#print axioms brownSeedMap_ι
#print axioms brownSeedMap_generator_surjective
