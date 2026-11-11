module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoChainTransport

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoChainTransport

/-!
概要：同じ実合成射を表す二組の後合成は、同じ指定同型の値を保持する。
方針：合成則と明示した実射の等式を、変数のまま合成する。
規約：端点の大きい定義を展開しない。使われ方：raw/native 輸送の指定比較への作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 二組の実後合成射の合成が等しければ、同じ指定同型への二段の作用も値を保つ。 -/
lemma functorIso_postcomp_pair_heq_of_pair_eq {A X Y Y' Z : SSet.{u}}
    {f g : A ⟶ X} (e : FunctorIso f g) (p : X ⟶ Y) (q : Y ⟶ Z)
    (r : X ⟶ Y') (s : Y' ⟶ Z) (h : p ≫ q = r ≫ s) :
    HEq ((e.postcomp p).postcomp q) ((e.postcomp r).postcomp s) :=
  (heq_of_eq (functorIso_postcomp_postcomp e p q)).trans
    ((functorIso_postcomp_heq_of_map_eq e h.symm).trans
      (heq_of_eq (functorIso_postcomp_postcomp e r s)).symm)

/-- 二組の実合成射の一致は、任意の実始域射の後でも保持される。 -/
lemma postcomp_pair_eq_of_pair_eq {C : Type*} [Category* C] {A X Y Y' Z : C}
    (f : A ⟶ X) (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Y') (s : Y' ⟶ Z)
    (h : p ≫ q = r ≫ s) : (f ≫ p) ≫ q = (f ≫ r) ≫ s := by
  simpa only [Category.assoc] using congrArg (fun k => f ≫ k) h

end SerrePositivity.InfinityCategories.F2
