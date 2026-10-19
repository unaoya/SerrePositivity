module

public import SerrePositivity.EInfinity.Surjection.CompositionUnit
public import SerrePositivity.EInfinity.TableReduction.CochainDegrees

/-!
# 全射語の整数複体の単位射

概要：Berger–Fresse §1.2.4 の一文字単位を整数複体の射として構成する。
方針：BE の単位射の後に構成済み TR を合成し、零次数で一文字語と一致することを示す。
規約：単位複体は既存のテンソル単位を使う。
使われ方：χ の Operad の unit と TR の単位保存。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Surjection

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：χ の一文字単位の整数複体の射（BF §1.2.4・§1.3）。
方針：BE の単位を整数 TR で送る。
規約：合成される二射はともに既に構成した複体の射。
使われ方：χ オペラッドの unit 成分。 -/
def complexUnit : 𝟙_ (Complex A) ⟶ complex A 1 :=
  BarrattEccles.unit A ≫ TableReduction.cochainMap A 1

/-- 概要：整数 TR は複体射の単位を保つ（BF §1.3）。
方針：χ の単位射の構成を評価する。
規約：等式は複体の射として成立する。
使われ方：TR オペラッド射の unit 条件。 -/
lemma complexUnit_comm :
    BarrattEccles.unit A ≫ TableReduction.cochainMap A 1 = complexUnit A := rfl

/-- 概要：χ の単位射の零次数は一文字単位のスカラー倍（BF §1.2.4）。
方針：BE の単位の評価と TR の単位生成元の保存を比較同型で移す。
規約：単位複体の零次数を A と標準同型で同定する。
使われ方：成分の単位則と整数複体の単位射を比較する。 -/
lemma complexUnit_zero_apply (a : A) :
    (complexUnit A).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv a) =
      a • (complexXIso A 1 0).inv (unitElement A) := by
  change (TableReduction.cochainMap A 1).f 0
    ((BarrattEccles.unit A).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv a)) = _
  rw [BarrattEccles.unit_zero_apply, map_smul]
  have h := TableReduction.cochainMap_nonpos_inv_apply A 1 0 (by decide)
    (BarrattEccles.normalizedGenerator A 1 0 BarrattEccles.unitSimplex)
  change (TableReduction.cochainMap A 1).f 0
    ((BarrattEccles.complexXIso A 1 0).inv
      (BarrattEccles.normalizedGenerator A 1 0 BarrattEccles.unitSimplex)) =
        (complexXIso A 1 0).inv
          (TableReduction.normalizedMap A 1 0
            (BarrattEccles.normalizedGenerator A 1 0 BarrattEccles.unitSimplex)) at h
  rw [h, normalizedMap_unit]

end SerrePositivity.EInfinity.Surjection
