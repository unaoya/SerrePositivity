module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorEnrichedNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：元の相対始域の前合成と、元の底上の射の native 後合成を厳密に交換する。
方針：同じ相対射を各次数・各入力で評価して比較する。
規約：底の等式を保持。使われ方：全選択族の指定比較を共通の全空間へ反映する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 相対前合成と指定した底上の射による後合成は、元の射そのもので厳密に可換する。 -/
lemma relativeFunctorPost_overPre {B C D E Q : SSet.{u}}
    (p : C ⟶ B) (d : D ⟶ B) (q : E ⟶ B) (r : Q ⟶ B)
    (t : D ⟶ C) (ht : t ≫ p = d) (f : E ⟶ Q) (hf : f ≫ r = q) :
    HomotopyLimits.relativeFunctorPost q r f hf p ≫
        relativeFunctorOverPre r (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht) =
      relativeFunctorOverPre q (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht) ≫
        HomotopyLimits.relativeFunctorPost q r f hf d := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
