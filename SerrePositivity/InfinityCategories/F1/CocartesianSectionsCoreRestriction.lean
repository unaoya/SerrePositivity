module

public import SerrePositivity.InfinityCategories.F1.CocartesianSectionsRestrictionLifting
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoreIsofibration

/-!
概要：任意の単射による cocartesian section の core の制限は Kan fibration。
方針：元の相対関手と section の同値持ち上げに、既存の core の充填性の判定を適用する。
規約：Fibration はホーンの持ち上げを表し、モデル圏の追加 instance は要求しない。
使われ方：区間 Hom 比較の骨格・境界に沿う Kan 空間の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

/-- cocartesian 標的の元の全相対 Hom の core は、単射による制限で Kan fibration を与える。 -/
lemma core_relativeFunctorPre_fibration_of_cocartesian
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (a : A ⟶ B) (i : D ⟶ A) [Mono i] :
    Fibration (quasicategoryCoreMap (relativeFunctorPre p a i)) :=
  F2.coreMap_fibration_of_kanEquivalenceLifting _
    (kanEquivalenceLifting_relativeFunctorPre_of_cocartesian p a i)

/-- 元の cocartesian section の core の単射による制限は Kan fibration。 -/
lemma core_kanCocartesianSectionsPre_fibration
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] :
    Fibration (quasicategoryCoreMap (kanCocartesianSectionsPre p i)) :=
  F2.coreMap_fibration_of_kanEquivalenceLifting _
    (kanEquivalenceLifting_kanCocartesianSectionsPre p i)

end SerrePositivity.InfinityCategories
