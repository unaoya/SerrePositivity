module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPrecomposition

/-!
概要：相対写像空間の底の表示変更と始域制限を厳密に交換する。
方針：底の等式を消去して同じ相対前合成へ戻す。
規約：指定等式による eqToHom を保持。使われ方：prism 終点の底変換の制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 底の同じ指定等式で移送してから制限しても、制限後に移送しても同じ射。 -/
lemma relativeFunctorPre_transport {A C E B : SSet.{u}} (p : E ⟶ B)
    {a b : A ⟶ B} (h : a = b) (s : C ⟶ A) :
    eqToHom (congrArg (relativeFunctorSpace p) h) ≫ relativeFunctorPre p b s =
      relativeFunctorPre p a s ≫
        eqToHom (congrArg (relativeFunctorSpace p) (congrArg (fun d => s ≫ d) h)) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.F2
