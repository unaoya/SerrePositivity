module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderChoice
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Complexes.CechAlexanderComplex
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechSiteAlexander

/-!
# 選んだ Čech–Alexander 包絡と既存 BigCech の自然な比較

## 概要
HasEnvelopes の選択を既存 BigCech の族へ自然同型で比較し、二つの交代余面複体へ移す。

## 方針
変数の普遍性による site の自然同型を、通常と剰余の加群の関手へ通す。

## 規約
BS 著者版 Construction 4.18。全単体射に自然で、係数 prism と剰余環を固定する。

## 使われ方
原典の選択による模型を、既存の具体的な大きい枠で計算するための比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory AlgebraicTopology
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

section ComplexFunctors
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u})

/-- 概要：site の余単体的対象を A 加群の交代余面複体に送る関手。
方針：構造代数から加群を取り、余単体的対象を右から合成する。
規約：BS 著者版 Construction 4.18。使われ方：模型間の自然同型を実際の複体へ移す。 -/
def prismSiteComplexFunctor :
    CosimplicialObject (PrismOver P R κ) ⥤ CochainComplex (ModuleCat.{u} A) ℕ :=
  (Functor.whiskeringRight _ _ _).obj
    (prismSiteAlgebras P R κ ⋙ Cech.underToModule (CommRingCat.of A)) ⋙
      alternatingCofaceMapComplex (ModuleCat.{u} A)

/-- 概要：site の余単体的対象を mod d の交代余面複体へ送る関手。
方針：剰余を A/d 加群として取り、A へ係数を制限する。
規約：BS 著者版 Construction 4.18。使われ方：mod d の計算模型の自然な比較。 -/
def prismSiteReducedComplexFunctor :
    CosimplicialObject (PrismOver P R κ) ⥤ CochainComplex (ModuleCat.{u} A) ℕ :=
  (Functor.whiskeringRight _ _ _).obj
    (prismSiteReducedAlgebras P R κ ⋙ Cech.underToModule (CommRingCat.of (A ⧸ P.ideal)) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk P.ideal)) ⋙
        alternatingCofaceMapComplex (ModuleCat.{u} A)
end ComplexFunctors

variable {Q : Poly (A ⧸ P.ideal)} {κ : Cardinal.{u}}
variable (h : HasEnvelopes P (polyCompletion P Q.n)) (hκ : cutoff A (polyCompletion P Q.n) ≤ κ)
variable (E : ∀ n, BigCechTerm P Q n) (hb : ∀ n, IsBoundedPrism (E n).prism)
variable (hs : ∀ n, Cardinal.mk (E n).carrier ≤ κ)

/-- 概要：選んだ包絡と既存の大きい枠は site 上で全単体射に自然に同型。
方針：両族の変数の普遍性から、恒等な添字写像を両向きに持ち上げる。
規約：BS 著者版 Construction 4.18。使われ方：原典の選択と既存の計算模型の比較。 -/
def cechAlexanderBigSiteIso :
    cechAlexander P (polyCompletion P Q.n) h κ hκ ≅ bigCechSiteAlexander E hb hs :=
  CechAlexanderPresentation.cosimplicialIso
    (fun n => (HasEnvelopes.term P (polyCompletion P Q.n) h n).sitePresentation κ hκ)
    (fun n => (E n).sitePresentation (hb n) (hs n))

/-- 概要：選んだ包絡の交代余面複体は既存 BigCech の実際の複体と同型。
方針：site の自然同型を A 加群の交代余面複体の関手に通す。
規約：BS 著者版 Construction 4.18。使われ方：既存の大きい枠による複体の計算。 -/
def cechAlexanderBigComplexIso :
    cechAlexanderComplex P (polyCompletion P Q.n) κ h hκ ≅
      (prismSiteComplexFunctor P (polyCompletion P Q.n) κ).obj (bigCechSiteAlexander E hb hs) :=
  (prismSiteComplexFunctor P (polyCompletion P Q.n) κ).mapIso
    (cechAlexanderBigSiteIso P h hκ E hb hs)

/-- 概要：mod d の交代余面複体も既存 BigCech の剰余の複体と同型。
方針：同じ site の自然同型を剰余の加群と交代余面複体へ通す。
規約：BS 著者版 Construction 4.18。使われ方：剰余の具体的な計算模型の比較。 -/
def cechAlexanderBigReducedComplexIso :
    cechAlexanderReducedComplex P (polyCompletion P Q.n) κ h hκ ≅
      (prismSiteReducedComplexFunctor P (polyCompletion P Q.n) κ).obj
        (bigCechSiteAlexander E hb hs) :=
  (prismSiteReducedComplexFunctor P (polyCompletion P Q.n) κ).mapIso
    (cechAlexanderBigSiteIso P h hκ E hb hs)

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 4.18" (partial := component) "大きい枠の Čech–Alexander 模型の項と座標変換（BS-D69 P2）。Δ を計算することは G9・G10 待ち ／ 11-11 更新 ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.cechAlexanderBigSiteIso
