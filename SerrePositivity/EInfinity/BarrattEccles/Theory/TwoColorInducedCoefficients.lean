module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCochainEquivalence
public import Mathlib.RepresentationTheory.Induced

/-!
# 二色の誘導表現と指定係数比較

## 概要
HA 3.2.4.7 の色付き入力語の分解に向け、誘導表現の余不変と二色部分群の係数を比較する。

## 方針
Mathlib の誘導表現とテンソル余不変の自然同型を、実際の arity の表現の複体へ適用する。

## 規約
係数射は既存の指定比較のまま。平坦性と群の位数の可逆性は要求しない。

## 使われ方
自由代数の Schur 表示の二色の成分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 実際の arity の係数を、対称群の表現の整数コチェイン複体にする。 -/
def arityRepresentationCochain (r : ℕ) :
    CochainComplex (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin r)))) ℤ :=
  representationCochainComplex (arityComplexAction A r)

/-- 実際の arity の複体の二色部分群への制限は、指定始域の複体である。 -/
def twoColorSourceRestrictionIso (m n : ℕ) :
    ((Rep.resFunctor (k := A) (twoColorPermutationHom.{u} m n).range.subtype).mapHomologicalComplex
      (.up ℤ)).obj (arityRepresentationCochain A (m + n)) ≅ twoColorSourceCochain A m n :=
  Iso.refl _

/-- 誘導した入力を持つ係数の余不変と、二色部分群への制限の指定同型。 -/
def twoColorInducedSourceIso (m n : ℕ) (V : Rep.{u} A (TwoColorGroup.{u} m n)) :
    (((Rep.coinvariantsTensor A (ULift.{u} (Equiv.Perm (Fin (m + n))))).obj
      (Rep.ind (twoColorPermutationHom.{u} m n).range.subtype V)).mapHomologicalComplex
        (.up ℤ)).obj (arityRepresentationCochain A (m + n)) ≅
    (((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj V).mapHomologicalComplex
      (.up ℤ)).obj (twoColorSourceCochain A m n) := by
  let R := Rep.resFunctor (k := A) (twoColorPermutationHom.{u} m n).range.subtype
  let T := (Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj V
  let B := arityRepresentationCochain A (m + n)
  let e : R ⋙ T ≅ R ⋙ T := Iso.refl _
  exact (NatIso.mapHomologicalComplex
    (Rep.coinvariantsTensorIndNatIso (twoColorPermutationHom.{u} m n).range.subtype V)
    (.up ℤ)).app B ≪≫
      ((Functor.mapHomologicalComplexCompIso (F := R) (G := T) e (.up ℤ)).app B).symm ≪≫
        (T.mapHomologicalComplex (.up ℤ)).mapIso (twoColorSourceRestrictionIso A m n)

/-- 誘導した色付き入力を持つ係数と、二色のテンソル係数の指定された同値。 -/
def twoColorInducedCoefficientHomotopyEquiv (m n : ℕ)
    (V : Rep.{u} A (TwoColorGroup.{u} m n)) :
    HomotopyEquiv
      ((((Rep.coinvariantsTensor A (ULift.{u} (Equiv.Perm (Fin (m + n))))).obj
        (Rep.ind (twoColorPermutationHom.{u} m n).range.subtype V)).mapHomologicalComplex
          (.up ℤ)).obj (arityRepresentationCochain A (m + n)))
      ((((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj V).mapHomologicalComplex
        (.up ℤ)).obj (twoColorTargetCochain A m n)) :=
  (HomotopyEquiv.ofIso (twoColorInducedSourceIso A m n V)).trans
    (twoColorCoefficientCoinvariantsHomotopyEquiv A m n V)

/-- 誘導表示の比較の順射は、指定同型の後の元の係数射である。 -/
@[simp]
lemma twoColorInducedCoefficientHomotopyEquiv_hom (m n : ℕ)
    (V : Rep.{u} A (TwoColorGroup.{u} m n)) :
    (twoColorInducedCoefficientHomotopyEquiv A m n V).hom =
      (twoColorInducedSourceIso A m n V).hom ≫
        (((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj V).mapHomologicalComplex
          (.up ℤ)).map (twoColorCoefficientCochainMap A m n) := rfl

end SerrePositivity.EInfinity.BarrattEccles
