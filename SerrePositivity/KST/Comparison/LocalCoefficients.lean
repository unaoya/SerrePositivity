module

public import SerrePositivity.KST.Comparison.Homology
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# 単体集合の局所係数の鎖複体

概要：元の圏上の可逆な係数系から実際の正規化鎖複体を構成する。
方針：元の圏から Δᵒᵖ への忘却に沿う左 Kan 拡張を取り、Moore 正規化を施す。
規約：Weibel K-book IV.1.6 の局所係数。元の圏は通常の単体の圏と逆向きである。
使われ方：plus の acyclic 性の局所係数を含む定式化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory AlgebraicTopology

/--
概要：単体集合上のアーベル群値局所係数系。
方針：元の圏上の関手で、全ての射の像が同型になるものを取る。
規約：Cegarra–Garzón, AGT 12 (2012), Remark 2.1 の局所化の記述の逆向きの模型。
使われ方：整数係数より一般の acyclic 性。
-/
structure LocalCoefficientSystem (X : SSet.{u}) where
  /-- 概要：各単体の係数群。方針：関手として保持。規約：元の圏上。使われ方：鎖複体。 -/
  coefficients : X.Elements ⥤ AddCommGrpCat.{u}
  /-- 概要：係数の輸送の可逆性。方針：全射で要求。規約：局所係数。使われ方：局所定数性。 -/
  transport_isIso : ∀ {x y : X.Elements} (f : x ⟶ y), IsIso (coefficients.map f)

/--
概要：任意の係数関手を単体的アーベル群へ送る関手。
方針：元の圏の忘却に沿う実際の左 Kan 拡張。
規約：局所係数以外にも定義できるが、その場合に局所定数性は主張しない。
使われ方：係数の鎖複体と係数変換。
-/
def coefficientSimplicialFunctor (X : SSet.{u}) :
    (X.Elements ⥤ AddCommGrpCat.{u}) ⥤ SimplicialObject AddCommGrpCat.{u} :=
  (Functor.Elements.π X).lan

/--
概要：局所係数系の正規化鎖複体。
方針：左 Kan 拡張で作った単体的アーベル群を Moore 正規化する。
規約：ホモロジー関手を任意に仮定する定義ではない。
使われ方：局所係数ホモロジーの計算。
-/
def localCoefficientChains (X : SSet.{u}) (L : LocalCoefficientSystem X) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  (normalizedMooreComplex _).obj ((coefficientSimplicialFunctor X).obj L.coefficients)

/--
概要：局所係数のホモロジー群。
方針：実際の正規化局所係数複体のホモロジーを取る。
規約：全自然数次数。
使われ方：acyclic 条件の各次数の群。
-/
abbrev localCoefficientHomology (X : SSet.{u}) (L : LocalCoefficientSystem X) (n : ℕ) :
    AddCommGrpCat.{u} := (localCoefficientChains X L).homology n

/--
概要：単体写像に沿った局所係数系の引き戻し。
方針：元の圏の関手に沿って係数を前合成する。
規約：輸送の可逆性は元の係数系から従う。
使われ方：局所係数ホモロジーの誘導射。
-/
def pullbackLocalCoefficients {X Y : SSet.{u}} (f : X ⟶ Y) (L : LocalCoefficientSystem Y) :
    LocalCoefficientSystem X where
  coefficients := f.mapElements ⋙ L.coefficients
  transport_isIso _g := L.transport_isIso _

/--
概要：引き戻し係数から標的の係数への単体的アーベル群の写像。
方針：標的の Kan 拡張の単位を元の圏の関手で引き戻し、源の Kan 拡張の普遍性を使う。
規約：全次数の面・退化と整合する自然変換。
使われ方：局所係数ホモロジーの実際の誘導写像。
-/
def localCoefficientSimplicialMap {X Y : SSet.{u}} (f : X ⟶ Y)
    (L : LocalCoefficientSystem Y) :
    (coefficientSimplicialFunctor X).obj (pullbackLocalCoefficients f L).coefficients ⟶
      (coefficientSimplicialFunctor Y).obj L.coefficients := by
  let t : (pullbackLocalCoefficients f L).coefficients ⟶
      Functor.Elements.π X ⋙ (coefficientSimplicialFunctor Y).obj L.coefficients :=
    Functor.whiskerLeft f.mapElements ((Functor.Elements.π Y).leftKanExtensionUnit L.coefficients)
  exact Functor.descOfIsLeftKanExtension _
    ((Functor.Elements.π X).leftKanExtensionUnit (pullbackLocalCoefficients f L).coefficients) _ t

/--
概要：局所係数の誘導鎖写像。
方針：Kan 拡張の普遍性で作った単体的写像に正規化を施す。
規約：源は引き戻し係数、標的は元の係数である。
使われ方：局所係数ホモロジーの写像。
-/
def localCoefficientChainsMap {X Y : SSet.{u}} (f : X ⟶ Y) (L : LocalCoefficientSystem Y) :
    localCoefficientChains X (pullbackLocalCoefficients f L) ⟶ localCoefficientChains Y L :=
  (normalizedMooreComplex _).map (localCoefficientSimplicialMap f L)

/--
概要：局所係数のホモロジーの誘導射。
方針：実際の正規化鎖写像にホモロジーを施す。
規約：全自然数次数で定義する。
使われ方：局所係数を含む acyclic 条件。
-/
abbrev localCoefficientHomologyMap {X Y : SSet.{u}} (f : X ⟶ Y)
    (L : LocalCoefficientSystem Y) (n : ℕ) :
    localCoefficientHomology X (pullbackLocalCoefficients f L) n ⟶
      localCoefficientHomology Y L n :=
  HomologicalComplex.homologyMap (localCoefficientChainsMap f L) n

/--
概要：全ての標的の局所係数についてホモロジー同型を誘導する条件。
方針：構成したホモロジー写像の可逆性を全係数・全次数で要求する。
規約：Weibel K-book IV.1.6 の局所係数による条件。ホモトピーファイバーとの同値は別定理を要する。
使われ方：plus の局所係数を含むホモロジー条件。
-/
def LocalHomologyIsomorphism {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (L : LocalCoefficientSystem Y) (n : ℕ), IsIso (localCoefficientHomologyMap f L n)

/--
概要：任意のアーベル群の定数局所係数系。
方針：元の圏からの定数関手を取り、輸送は恒等射とする。
規約：定数整数係数との正規化比較は別途証明する。
使われ方：整数ホモロジーを局所係数の帰結として接続する。
-/
def constantLocalCoefficients (X : SSet.{u}) (G : AddCommGrpCat.{u}) :
    LocalCoefficientSystem X where
  coefficients := (Functor.const X.Elements).obj G
  transport_isIso _ := by dsimp; infer_instance

end SerrePositivity.KST.Comparison
