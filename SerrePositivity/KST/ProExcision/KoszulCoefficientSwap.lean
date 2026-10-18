module

public import SerrePositivity.KST.ProExcision.SpectralPro

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Koszul 係数の左右交換と pro-零性

概要：次頁計算の右係数テンソルを、Lemma 4.9 で用いた左係数モデルへ自然に移す。
方針：加群の対称テンソルの標準同型を複体とホモロジーへ持ち上げる。
規約：交換は複体の次数を持たない係数加群との点ごとの交換であり、全複体の符号付き交換とは区別する。
使われ方：KST Lemma 4.10 の E₂ の pro-零性への移行。
-/

universe u v w v' w'

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

/-- 概要：関手の自然同型は像の塔の pro-零性を移す。
方針：自然同型の逆をレベル同型の射にし、既存の pro-零性移送を適用する。
規約：零化指数は変わらない。使われ方：KST Lemma 4.9・4.10 の係数モデルの交換。 -/
theorem IsProZero.of_natIso
    {C : Type v} [Category.{v'} C] {D : Type w} [Category.{w'} D] [HasZeroMorphisms D]
    (X : Tower C) {F G : C ⥤ D} (e : F ≅ G) (hG : IsProZero (X.map G)) :
    IsProZero (X.map F) := by
  let f := X.mapNatTrans e.inv
  have hf (n : ℕ) : IsIso (f.app n) := by
    dsimp [f, Tower.mapNatTrans]
    infer_instance
  exact IsProZero.of_levelwiseIso f hG

variable {R : Type u} [CommRing R]

/-- 概要：右係数テンソルと左係数テンソルを点ごとの複体として自然に同定する。
方針：加群の標準組紐同型を複体関手へ持ち上げる。
規約：係数の平坦性は不要。使われ方：KST Lemma 4.10 の右係数模型から Lemma 4.9 への接続。 -/
def pointwiseTensorSwapIso (M : ModuleCat.{u} R) :
    (tensorRight M).mapHomologicalComplex (.up ℤ) ≅
      (tensorLeft M).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight M).symm (.up ℤ)

/-- 概要：点ごとの係数の左右交換はホモロジーにも自然同型を与える。
方針：複体関手の交換同型にホモロジー関手を後合成する。
規約：任意のコホモロジー次数 q。使われ方：KST Lemma 4.10 の E₂ と既存の pro-零性の比較。 -/
def pointwiseTensorSwapHomologyIso (M : ModuleCat.{u} R) (q : ℤ) :
    (tensorRight M).mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor _ _ q ≅
      (tensorLeft M).mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor _ _ q :=
  Functor.isoWhiskerRight (pointwiseTensorSwapIso M) (homologyFunctor _ _ q)

/-- 概要：右係数模型の Koszul ホモロジーの塔。
方針：実際の Koszul 冪遷移に点ごとの右テンソルとホモロジーを施す。
規約：係数加群は固定。使われ方：KST Lemma 4.10 の E₂ の定数係数部分。 -/
def koszulRightTensorHomologyTower {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (q : ℤ) : Tower (ModuleCat.{u} R) :=
  (koszulTower z).map ((tensorRight M).mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor _ _ q)

/-- 概要：有限生成加群係数の右 Koszul ホモロジーも負のコホモロジー次数で pro-零。
方針：係数左右交換の自然同型で、証明済みの Lemma 4.9 の左係数模型へ移す。
規約：追加の平坦性は不要。使われ方：KST Lemma 4.10 の E₂ の消滅。 -/
theorem koszulRightTensorHomologyTower_isProZero [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (q : ℤ) (hq : q < 0) : IsProZero (koszulRightTensorHomologyTower z M q) :=
  IsProZero.of_natIso (koszulTower z) (pointwiseTensorSwapHomologyIso M q)
    (koszulTensorHomologyTower_isProZero z M q hq)


end SerrePositivity.KST.ProExcision
