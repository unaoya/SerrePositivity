module

public import SerrePositivity.InfinityCategories.F2.Ind.CommaPostcompIso
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaRestriction

/-!
概要：同型による元の形状制限は、元の diagram comma の同型である。
方針：内部 Hom の前合成と宇宙移送が同型を保つことを使う。
規約：元の制限写像そのものの同型性。
使われ方：全体に等しい下方部分での指定余錐持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：同型の形状制限は同型。
方針：内部 Hom の関手性と comma 同型。規約：元の全射。使われ方：帰納基底。 -/
lemma diagramCommaRestriction_isIso (κ : Cardinal.{u}) {J K C : SSet.{u}}
    [Quasicategory C] (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    (f : J ⟶ K) [IsIso f] : IsIso (diagramCommaRestriction κ D f) := by
  letI : IsIso ((pre f).app C) :=
    NatIso.isIso_app_of_isIso (internalHom.map f.op) C
  letI : IsIso ((pre ((SSet.uliftFunctor.{u + 1, u}).map f)).app (IndInfinity κ C)) :=
    NatIso.isIso_app_of_isIso
      (internalHom.map ((SSet.uliftFunctor.{u + 1, u}).map f).op) (IndInfinity κ C)
  exact commaPostcomp_isIso _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
