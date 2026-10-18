module

public import SerrePositivity.KST.Comparison.LocalCoefficientFibers
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# 標準単体上の局所係数の自明化

概要：標準単体上の局所係数系を、恒等単体の係数群の定数係数系と同定する。
方針：元の圏の初対象からの輸送を使い、その可逆性から自然同型を作る。
規約：Weibel K-book IV.1.6 の horn と局所係数の計算。
使われ方：局所係数の horn 添付のホモロジー保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

/--
概要：元の圏に初対象がある局所係数系は定数係数系と自然同型である。
方針：初対象からの唯一の射に沿う可逆な輸送を各成分とする。
規約：初対象の係数群を使う。
使われ方：標準単体上の局所係数の自明化。
-/
def localCoefficientConstIsoOfInitial {X : SSet.{u}} (L : LocalCoefficientSystem X)
    (e : X.Elements) (he : IsInitial e) :
    (constantLocalCoefficients X (L.coefficients.obj e)).coefficients ≅ L.coefficients := by
  have (a : X.Elements) : IsIso (L.coefficients.map (he.to a)) := L.transport_isIso _
  refine NatIso.ofComponents (fun a => asIso (L.coefficients.map (he.to a))) ?_
  intro a b f
  change L.coefficients.map (he.to b) = L.coefficients.map (he.to a) ≫ L.coefficients.map f
  rw [← L.coefficients.map_comp]
  exact congrArg L.coefficients.map (he.hom_ext _ _)

/--
概要：標準単体は自分自身の恒等単体で表現される。
方針：Mathlib の標準単体の要素と単体圏の射の同値を使う。
規約：単体集合の値の宇宙を保つ。
使われ方：元の圏の初対象の構成。
-/
def standardSimplexRepresentableBy (n : ℕ) : (Δ[n] : SSet.{u}).RepresentableBy ⦋n⦌ where
  homEquiv := SSet.stdSimplex.objEquiv.symm
  homEquiv_comp _ _ := rfl

/--
概要：標準単体の元の圏の恒等単体。
方針：表現可能性に対応する普遍元を取る。
規約：任意の自然数次元。
使われ方：局所係数の自明化の基準となる係数群。
-/
abbrev standardSimplexIdentityElement (n : ℕ) : (Δ[n] : SSet.{u}).Elements :=
  Functor.Elements.initialOfRepresentableBy (standardSimplexRepresentableBy n)

/--
概要：標準単体の元の圏で恒等単体は初対象である。
方針：表現可能な関手の元の圏の初対象の実際の普遍性を適用する。
規約：全ての単体からの射ではなく、恒等単体からの射が唯一である。
使われ方：定数局所係数との比較。
-/
def standardSimplexIdentityElementIsInitial (n : ℕ) :
    IsInitial (standardSimplexIdentityElement.{u} n) :=
  Functor.Elements.isInitialOfRepresentableBy (standardSimplexRepresentableBy n)

/--
概要：標準単体上の局所係数系は恒等単体の係数群の定数係数系と自然同型である。
方針：元の圏の初対象からの可逆な輸送を適用する。
規約：自明化を追加の仮定として置かない。
使われ方：horn と標準単体の局所係数ホモロジーの比較。
-/
def standardSimplexLocalCoefficientTrivialization (n : ℕ)
    (L : LocalCoefficientSystem (Δ[n] : SSet.{u})) :
    (constantLocalCoefficients (Δ[n] : SSet.{u})
      (L.coefficients.obj (standardSimplexIdentityElement n))).coefficients ≅ L.coefficients :=
  localCoefficientConstIsoOfInitial L _ (standardSimplexIdentityElementIsInitial n)

/--
概要：係数系の自然同型は実際の正規化鎖複体の同型を誘導する。
方針：係数の Kan 拡張と Moore 正規化の関手へ自然同型を渡す。
規約：同じ単体集合上の係数系の比較。
使われ方：自明化をホモロジーへ移す。
-/
def localCoefficientChainsIso {X : SSet.{u}} {L K : LocalCoefficientSystem X}
    (e : L.coefficients ≅ K.coefficients) :
    localCoefficientChains X L ≅ localCoefficientChains X K :=
  (normalizedMooreComplex _).mapIso ((coefficientSimplicialFunctor X).mapIso e)

/--
概要：局所係数系の自然同型は局所係数ホモロジーの同型を誘導する。
方針：構成した鎖複体の同型にホモロジーを施す。
規約：全自然数次数。
使われ方：標準単体の局所係数の計算。
-/
def localCoefficientHomologyIso {X : SSet.{u}} {L K : LocalCoefficientSystem X}
    (e : L.coefficients ≅ K.coefficients) (n : ℕ) :
    localCoefficientHomology X L n ≅ localCoefficientHomology X K n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (localCoefficientChainsIso e)

end SerrePositivity.KST.Comparison
