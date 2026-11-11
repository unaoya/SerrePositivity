module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverPrecomposition

/-!
概要：底上の始域制限を元の相対前合成と指定した底の等式移送で表示する。
方針：底の等式を除去して同じ fiber への持ち上げへ戻す。
規約：指定した底の等式を保持。使われ方：小宇宙の始域制限と prism 比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 底上の制限は相対前合成の後で指定した底の等式に沿って移送したもの。 -/
lemma relativeFunctorOverPre_eq_pre_transport {A C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (d : C ⟶ B) (s : C ⟶ A) (hs : s ≫ a = d) :
    relativeFunctorOverPre p (Over.homMk (U := Over.mk d) (V := Over.mk a) s hs) =
      relativeFunctorPre p a s ≫ eqToHom (congrArg (relativeFunctorSpace p) hs) := by
  subst d
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.F2
