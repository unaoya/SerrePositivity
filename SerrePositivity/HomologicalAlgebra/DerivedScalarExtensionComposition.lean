module

public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence

/-!
# 導来係数拡大の合成と可換四角形

## 概要
上に有界な導来対象の係数拡大を、合成された環射と二段階の環射で比較する。

## 方針
通常の係数拡大の合成同型を、同じ射影模型に適用する。

## 規約
環射の平坦性を仮定しない。既存の導来係数拡大の標準模型を用いる。

## 使われ方
BS 著者版 Example 7.9 の生成元剰余と初期関係の商、および底変換。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

variable {R S T V : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing V]

/-- 概要：合成された環射に沿う導来係数拡大は、二段階の導来係数拡大と同型。
方針：元の射影模型の通常係数拡大を合成し、第二段の導来模型と比較する。
規約：任意の可換環射に適用できる。
使われ方：生成元と関係による二段階の剰余。 -/
def boundedAboveDerivedBaseChangeCompositionIso (f : R →+* S) (g : S →+* T)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (boundedAboveDerivedBaseChange (g.comp f)).obj X ≅
      (boundedAboveDerivedBaseChange g).obj ((boundedAboveDerivedBaseChange f).obj X) :=
  ObjectProperty.isoMk _
    (DerivedCategory.Q.mapIso
        (baseChangeCompIso f g (boundedAboveDerivedChosenModel X).complex).symm ≪≫
      (boundedAboveDerivedBaseChangeModelIso g ((boundedAboveDerivedBaseChange f).obj X)
        (boundedAboveDerivedBaseChangeModel f X)).symm)

/-- 概要：可換な環射の四角形は、二つの二段階導来係数拡大を同定する。
方針：各段を合成された環射への係数拡大に移し、可換性を使う。
規約：平坦性と Tor 消滅を仮定しない。
使われ方：BS 著者版 Example 7.9 の剰余の四角形。 -/
def boundedAboveDerivedBaseChangeSquareIso
    (f : R →+* S) (g : S →+* T) (f' : R →+* V) (g' : V →+* T)
    (h : g.comp f = g'.comp f') (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (boundedAboveDerivedBaseChange g).obj ((boundedAboveDerivedBaseChange f).obj X) ≅
      (boundedAboveDerivedBaseChange g').obj ((boundedAboveDerivedBaseChange f').obj X) :=
  (boundedAboveDerivedBaseChangeCompositionIso f g X).symm ≪≫
    eqToIso (congrArg (fun k : R →+* T => (boundedAboveDerivedBaseChange k).obj X) h) ≪≫
    boundedAboveDerivedBaseChangeCompositionIso f' g' X

end SerrePositivity
