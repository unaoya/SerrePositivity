module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.NonpositiveHomotopyRestriction
public import Mathlib.Algebra.Homology.Single

/-!
# 零次単一複体の非正次数への制限

## 概要
HA 3.2.4.7 の二色係数の指定増大の値を、鎖複体の零次単一複体に同定する。

## 方針
零次には指定された単一成分の同型を使い、他の次数には零対象の同型を使う。

## 規約
零次成分の比較は `singleObjXSelf` の順射そのもの。

## 使われ方
実際のテンソル増大の忘却と鎖ホモトピー同値の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomologicalComplex
variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- 零次単一複体の制限の各次数の、指定された成分同型。 -/
def nonpositiveSingleComponentIso (V : C) (q : ℕ) :
    ((single C (.up ℤ) 0).obj V).X (-(q : ℤ)) ≅
      ((ChainComplex.single₀ C).obj V).X q := by
  cases q with
  | zero => exact singleObjXSelf (.up ℤ) 0 V
  | succ q =>
    exact (isZero_single_obj_X (.up ℤ) 0 V (-(q + 1 : ℕ) : ℤ) (by omega)).iso
      (isZero_single_obj_X (.down ℕ) 0 V (q + 1) (by omega))

/-- 零次のコチェイン単一複体を制限すると、零次の鎖単一複体になる。 -/
def nonpositiveSingleIso (V : C) :
    ((single C (.up ℤ) 0).obj V).restriction ComplexShape.embeddingDownNat ≅
      (ChainComplex.single₀ C).obj V :=
  HomologicalComplex.Hom.isoOfComponents (nonpositiveSingleComponentIso V) (by
    intro i j h
    change _ ≫ ((single C (.down ℕ) 0).obj V).d i j =
      ((single C (.up ℤ) 0).obj V).d (-(i : ℤ)) (-(j : ℤ)) ≫ _
    simp only [single_obj_d, comp_zero, zero_comp])

/-- 零次成分では元の指定された単一成分の同型を保持する。 -/
@[simp]
lemma nonpositiveSingleIso_hom_f_zero (V : C) :
    (nonpositiveSingleIso V).hom.f 0 = (singleObjXSelf (.up ℤ) 0 V).hom := rfl

end SerrePositivity.EInfinity
