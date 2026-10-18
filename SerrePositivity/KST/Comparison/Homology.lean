module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# 単体集合の正規化された整数ホモロジー

概要：自由単体的アーベル群の正規化 Moore 複体の実際のホモロジーを構成する。
方針：Mathlib の自由関手と正規化・alternating face map complex の実際の鎖ホモトピー同値を使う。
規約：Weibel K-book III、Waldhausen LNM 1126 §1.7・§1.8・§2.3 の整数係数。非正規化複体と区別する。
使われ方：plus 構成のホモロジー同型と acyclic map の整数係数の部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory AlgebraicTopology

/--
概要：単体集合 X から自由単体的アーベル群 ℤ[X] を作る関手。
方針：各次数と各単体作用に AddCommGrpCat.free を施す。
規約：単体集合の値宇宙を保つ。
使われ方：整数鎖複体の入力。
-/
def freeAbelianSimplicialFunctor : SSet.{u} ⥤ SimplicialObject AddCommGrpCat.{u} :=
  (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free

/--
概要：整数係数の非正規化鎖複体の関手。
方針：自由単体的アーベル群の alternating face map complex を取る。
規約：退化単体をまだ含む複体である。
使われ方：単体的ホモトピーと鎖ホモトピーの比較。
-/
def unnormalizedIntegralChains : SSet.{u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  freeAbelianSimplicialFunctor ⋙ alternatingFaceMapComplex _

/--
概要：整数係数の正規化鎖複体の関手。
方針：自由単体的アーベル群の正規化 Moore 複体を取る。
規約：正の面の核の交わりと零番目の面による微分を使う。
使われ方：整数ホモロジーの実際の定義。
-/
def normalizedIntegralChains : SSet.{u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  freeAbelianSimplicialFunctor ⋙ normalizedMooreComplex _

/--
概要：正規化鎖複体から非正規化鎖複体への自然な包含。
方針：Mathlib の Moore 複体の包含を自由単体的アーベル群へ適用する。
規約：全ての単体写像との自然性を含む。
使われ方：二つのホモロジー模型の自然な比較。
-/
def normalizationInclusion : normalizedIntegralChains.{u} ⟶ unnormalizedIntegralChains :=
  Functor.whiskerLeft freeAbelianSimplicialFunctor (inclusionOfMooreComplex _)

/--
概要：正規化と非正規化の整数鎖複体は鎖ホモトピー同値である。
方針：Mathlib の P∞ による実際の鎖ホモトピー同値を適用する。
規約：鎖写像と逆鎖写像、両合成の鎖ホモトピーを含む。
使われ方：正規化によるホモロジーの比較の証明。
-/
def normalizationHomotopyEquiv (X : SSet.{u}) :
    HomotopyEquiv (normalizedIntegralChains.obj X) (unnormalizedIntegralChains.obj X) :=
  DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

/--
概要：正規化された整数ホモロジーの関手。
方針：正規化鎖複体に実際のホモロジー関手を合成する。
規約：次数 n は自然数。
使われ方：単体写像が誘導するホモロジーの射。
-/
def integralHomologyFunctor (n : ℕ) : SSet.{u} ⥤ AddCommGrpCat.{u} :=
  normalizedIntegralChains ⋙ HomologicalComplex.homologyFunctor _ _ n

/--
概要：単体集合の次数 n の整数ホモロジー群。
方針：正規化されたホモロジー関手の対象として取る。
規約：ホモロジーを任意の関手として仮定しない。
使われ方：plus 構成のホモロジー同型の主張。
-/
abbrev integralHomology (X : SSet.{u}) (n : ℕ) : AddCommGrpCat.{u} :=
  (integralHomologyFunctor n).obj X

/--
概要：単体写像が誘導する整数ホモロジーの射。
方針：正規化鎖複体の実際の誘導写像にホモロジーを施す。
規約：恒等・合成の法則は関手の法則で与えられる。
使われ方：整数ホモロジー同型の判定。
-/
abbrev integralHomologyMap {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralHomology X n ⟶ integralHomology Y n :=
  (integralHomologyFunctor n).map f

/--
概要：非正規化された整数鎖複体のホモロジー関手。
方針：alternating face map complex にホモロジーを施す。
規約：定義上の整数ホモロジーとは比較同型で結ぶ。
使われ方：鎖ホモトピー不変性の移送。
-/
def unnormalizedIntegralHomologyFunctor (n : ℕ) : SSet.{u} ⥤ AddCommGrpCat.{u} :=
  unnormalizedIntegralChains ⋙ HomologicalComplex.homologyFunctor _ _ n

/--
概要：正規化と非正規化の整数ホモロジーの同型。
方針：実際の鎖ホモトピー同値をホモロジーの同型へ渡す。
規約：比較射は Moore 複体の包含の誘導写像。
使われ方：二つの鎖複体のホモロジー計算の一致。
-/
def normalizationHomologyIso (X : SSet.{u}) (n : ℕ) :
    integralHomology X n ≅ (unnormalizedIntegralHomologyFunctor n).obj X :=
  (normalizationHomotopyEquiv X).toHomologyIso n

/--
概要：正規化された整数ホモロジーと非正規化のものの自然同型。
方針：包含の自然性にホモロジーを施して各対象の同型をまとめる。
規約：任意の単体写像との自然性。
使われ方：ホモトピー不変性と相対ホモロジーの比較。
-/
def normalizationHomologyNatIso (n : ℕ) :
    integralHomologyFunctor.{u} n ≅ unnormalizedIntegralHomologyFunctor n :=
  NatIso.ofComponents (fun X => normalizationHomologyIso X n) (by
    intro X Y f
    change HomologicalComplex.homologyMap (normalizedIntegralChains.map f) n ≫
        HomologicalComplex.homologyMap (normalizationInclusion.app Y) n =
      HomologicalComplex.homologyMap (normalizationInclusion.app X) n ≫
        HomologicalComplex.homologyMap (unnormalizedIntegralChains.map f) n
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun g => HomologicalComplex.homologyMap g n)
      (normalizationInclusion.naturality f))

end SerrePositivity.KST.Comparison
