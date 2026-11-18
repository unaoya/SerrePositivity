module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainCompositionLaws
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainPermutation
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoalgebraRestriction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.OperadMap

/-!
模型。文献の定義との比較は後で
# 全単体集合の同じBF切断によるχ・E余代数

Berger–Fresse §2.2・§3.1、M14 L18、報告 §393。
全整数複体射の三公理と自然性を束ね、同じTRに沿って制限する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 元の全BF切断による一般正規化単体のχ余代数（BF §2.2・§3.1）。 -/
def surjectionCoalgebra (S : SSet.{0}) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.operad A).Coalgebra where
  carrier := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S
  coaction := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S
  equivariance := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_equivariance A S
  unit_coaction := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_unit A S
  comp_coaction := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coaction_comp_all A S

/-- 同じ正規化鎖の写像は全BF余作用を保つ（BF §2.2・§3.1）。 -/
def surjectionCoalgebraMap {S T : SSet.{0}} (f : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.surjectionCoalgebra A S ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.surjectionCoalgebra A T where
  hom := (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f
  comm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coaction_natural A f

/-- 元の全単体集合と写像のχ余代数関手（BF §2.2・§3.1）。 -/
def surjectionCoalgebraFunctor : SSet.{0} ⥤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.operad A).Coalgebra where
  obj := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.surjectionCoalgebra A
  map := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.surjectionCoalgebraMap A
  map_id S := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom.ext
    exact (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map_id S
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom.ext
    exact (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map_comp f g

/-- 同じ一般TRを元のBF余作用へ前置したE余代数（BF §3.1）。 -/
def barrattEcclesCoalgebra (S : SSet.{0}) : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Coalgebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictCoalgebraObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.operadMap A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.surjectionCoalgebra A S)

/-- 同じTRによる制限は底の鎖写像を保つ（BF §3.1）。 -/
def barrattEcclesCoalgebraMap {S T : SSet.{0}} (f : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.barrattEcclesCoalgebra A S ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.barrattEcclesCoalgebra A T :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictCoalgebraMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.operadMap A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.surjectionCoalgebraMap A f)

/-- 一般TRによる同じE余代数の全関手（BF §3.1）。 -/
def barrattEcclesCoalgebraFunctor : SSet.{0} ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Coalgebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.surjectionCoalgebraFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictCoalgebra (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.operadMap A)

/-- 制限後の作用は元の指定TRと同じBF切断作用の合成（BF §3.1）。 -/
lemma barrattEcclesCoalgebra_coaction (S : SSet.{0}) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.barrattEcclesCoalgebra A S).coaction n =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.operadMap A).map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S n := rfl

/-- 制限後の底の射も元の正規化写像そのもの（BF §3.1）。 -/
lemma barrattEcclesCoalgebraMap_hom {S T : SSet.{0}} (f : S ⟶ T) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.barrattEcclesCoalgebraMap A f).hom = (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f := rfl

/-- 構成した同じTR制限の射は全指定余作用を保つ（BF §3.1）。 -/
lemma barrattEcclesCoalgebraMap_comm {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).arity n ◁ (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.barrattEcclesCoalgebra A T).coaction n =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.barrattEcclesCoalgebra A S).coaction n ≫
        _root_.SerrePositivity.TensorPowers.map ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) n :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.barrattEcclesCoalgebraMap A f).comm n

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
