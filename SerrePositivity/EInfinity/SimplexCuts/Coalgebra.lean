module

public import SerrePositivity.EInfinity.SimplexCuts.CochainCompositionLaws
public import SerrePositivity.EInfinity.SimplexCuts.CochainPermutation
public import SerrePositivity.EInfinity.SimplexCuts.CochainUnit
public import SerrePositivity.EInfinity.Operad.CoalgebraRestriction
public import SerrePositivity.EInfinity.TableReduction.OperadMap

/-!
# 全単体集合の同じBF切断によるχ・E余代数

Berger–Fresse §2.2・§3.1、M14 L18、報告 §393。
全整数複体射の三公理と自然性を束ね、同じTRに沿って制限する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 元の全BF切断による一般正規化単体のχ余代数（BF §2.2・§3.1）。 -/
def surjectionCoalgebra (S : SSet.{0}) : (Surjection.operad A).Coalgebra where
  carrier := chains A S
  coaction := cochainAction A S
  equivariance := cochainAction_equivariance A S
  unit_coaction := cochainAction_unit A S
  comp_coaction := coaction_comp_all A S

/-- 同じ正規化鎖の写像は全BF余作用を保つ（BF §2.2・§3.1）。 -/
def surjectionCoalgebraMap {S T : SSet.{0}} (f : S ⟶ T) :
    surjectionCoalgebra A S ⟶ surjectionCoalgebra A T where
  hom := (BarrattEccles.normalizedFunctor A).map f
  comm := coaction_natural A f

/-- 元の全単体集合と写像のχ余代数関手（BF §2.2・§3.1）。 -/
def surjectionCoalgebraFunctor : SSet.{0} ⥤ (Surjection.operad A).Coalgebra where
  obj := surjectionCoalgebra A
  map := surjectionCoalgebraMap A
  map_id S := by
    apply Operad.CoalgebraHom.ext
    exact (BarrattEccles.normalizedFunctor A).map_id S
  map_comp f g := by
    apply Operad.CoalgebraHom.ext
    exact (BarrattEccles.normalizedFunctor A).map_comp f g

/-- 同じ一般TRを元のBF余作用へ前置したE余代数（BF §3.1）。 -/
def barrattEcclesCoalgebra (S : SSet.{0}) : (BarrattEccles.operad A).Coalgebra :=
  Operad.restrictCoalgebraObj (TableReduction.operadMap A) (surjectionCoalgebra A S)

/-- 同じTRによる制限は底の鎖写像を保つ（BF §3.1）。 -/
def barrattEcclesCoalgebraMap {S T : SSet.{0}} (f : S ⟶ T) :
    barrattEcclesCoalgebra A S ⟶ barrattEcclesCoalgebra A T :=
  Operad.restrictCoalgebraMap (TableReduction.operadMap A) (surjectionCoalgebraMap A f)

/-- 一般TRによる同じE余代数の全関手（BF §3.1）。 -/
def barrattEcclesCoalgebraFunctor : SSet.{0} ⥤ (BarrattEccles.operad A).Coalgebra :=
  surjectionCoalgebraFunctor A ⋙ Operad.restrictCoalgebra (TableReduction.operadMap A)

/-- 制限後の作用は元の指定TRと同じBF切断作用の合成（BF §3.1）。 -/
lemma barrattEcclesCoalgebra_coaction (S : SSet.{0}) (n : ℕ) :
    (barrattEcclesCoalgebra A S).coaction n =
      ((TableReduction.operadMap A).map.app (FiniteBijection.of n) ▷ chains A S) ≫
        cochainAction A S n := rfl

/-- 制限後の底の射も元の正規化写像そのもの（BF §3.1）。 -/
lemma barrattEcclesCoalgebraMap_hom {S T : SSet.{0}} (f : S ⟶ T) :
    (barrattEcclesCoalgebraMap A f).hom = (BarrattEccles.normalizedFunctor A).map f := rfl

/-- 構成した同じTR制限の射は全指定余作用を保つ（BF §3.1）。 -/
lemma barrattEcclesCoalgebraMap_comm {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ) :
    ((BarrattEccles.operad A).arity n ◁ (BarrattEccles.normalizedFunctor A).map f) ≫
        (barrattEcclesCoalgebra A T).coaction n =
      (barrattEcclesCoalgebra A S).coaction n ≫
        TensorPowers.map ((BarrattEccles.normalizedFunctor A).map f) n :=
  (barrattEcclesCoalgebraMap A f).comm n

end SerrePositivity.EInfinity.SimplexCuts
