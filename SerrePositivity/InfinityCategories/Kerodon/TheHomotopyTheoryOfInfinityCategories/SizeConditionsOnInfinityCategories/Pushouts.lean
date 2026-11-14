module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.UniversePullbacks

/-!
概要：元の単体集合の pushout を宇宙持ち上げ後も同じ四射の pushout として保持する。
方針：型の ULift の余極限保存を単体対象の後合成へ移す。
規約：貼付け写像の単射性や Kan 性は要求しない。
使われ方：セル貼合せの source と分類先の宇宙を揃える。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 元の単体集合の同じ span の pushout を ULift は保存する。 -/
instance uliftSSetFunctor_preservesPushout {A B C : SSet.{u}} (f : A ⟶ B) (g : A ⟶ C) :
    PreservesColimit (span f g) (SSet.uliftFunctor.{v, u}) := by
  change PreservesColimit (span f g)
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (Type (max u v))).obj
      CategoryTheory.uliftFunctor.{v, u})
  infer_instance

/-- 同じ四射で与えた pushout は宇宙持ち上げ後も pushout。 -/
lemma uliftSSet_isPushout {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) :
    IsPushout ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g)
      ((SSet.uliftFunctor.{v, u}).map i) ((SSet.uliftFunctor.{v, u}).map j) :=
  h.map (SSet.uliftFunctor.{v, u})

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
