module
public import SerrePositivity.DifferentialGraded.Resolution.Free.EvaluationComposition
public import Mathlib.Data.ZMod.Basic

/-! # 自由pathの右単位と任意dg圏への評価の監査

## 概要
自由pathの右単位と任意dg圏への評価の監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.FreeDGCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]
  (E : Type w) [DGCategory A E]

example (K : ComplexQuiver A D) (x y : D) :
    (homComplex A D K x y ◁ unitInclusion A D K y) ≫ composition A D K x y y =
      (ρ_ (homComplex A D K x y)).hom := composition_right_unit A D K x y

-- 標的Eのsmallness、元の辺のK-flat性、有界性は要求しない。
example (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y z : D) :
    composition A D K x y z ≫ homEvaluation A D E K o f x z =
      (homEvaluation A D E K o f x y ⊗ₘ homEvaluation A D E K o f y z) ≫
        eComp (Complex A) (o x) (o y) (o z) :=
  homEvaluation_composition A D E K o f x y z

example (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x : D) :
    unitInclusion A D K x ≫ homEvaluation A D E K o f x x = eId (Complex A) (o x) :=
  unitInclusion_homEvaluation A D E K o f x

example (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y))
    (p q : List D) (x y z : D) :
    (wordConcatenationIso A D K p q x y z).hom ≫
        wordEvaluation A D E K o f (concatenate D p q y) x z =
      (wordEvaluation A D E K o f p x y ⊗ₘ wordEvaluation A D E K o f q y z) ≫
        eComp (Complex A) (o x) (o y) (o z) :=
  wordEvaluation_concatenation A D E K o f p q x y z

example (D : Type v) [Small.{0} D] (E : Type w) [DGCategory (ZMod 2) E]
    (K : ComplexQuiver (ZMod 2) D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex (ZMod 2)] o y)) (x y z : D) :
    composition (ZMod 2) D K x y z ≫ homEvaluation (ZMod 2) D E K o f x z =
      (homEvaluation (ZMod 2) D E K o f x y ⊗ₘ homEvaluation (ZMod 2) D E K o f y z) ≫
        eComp (Complex (ZMod 2)) (o x) (o y) (o z) :=
  homEvaluation_composition (ZMod 2) D E K o f x y z

#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathComposition_right_unit
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_path_unit
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_right_unit
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.wordEvaluation
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathEvaluation
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homEvaluation
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathInclusion_homEvaluation
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.unitInclusion_homEvaluation
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.edgeInclusion_homEvaluation
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.evaluation_tensor_assoc
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.wordEvaluation_concatenation
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathEvaluation_composition
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homEvaluation_composition
