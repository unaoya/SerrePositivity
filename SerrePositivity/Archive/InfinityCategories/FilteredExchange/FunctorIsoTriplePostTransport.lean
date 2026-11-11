module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoChainTransport

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoChainTransport

/-!
概要：元の指定後合成射の三射への分解を、同じ指定関手同型の三段の像へ移す。
方針：射の等式と二段の後合成則を抽象的に合成する。
規約：元の指定値と射等式を保持。使われ方：raw fiber 二面比較の輸送後の像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ指定射の三段の分解は、同じ指定同型への三段の後合成の値を保持する。 -/
lemma functorIso_postcomp_triple_transport_heq {A B C D E : SSet.{u}}
    {f g : A ⟶ B} (e : FunctorIso f g) (p : B ⟶ C) (t : C ⟶ D) (v : D ⟶ E)
    (q : B ⟶ E) (hq : q = p ≫ t ≫ v) :
    HEq (e.postcomp q) (((e.postcomp p).postcomp t).postcomp v) := by
  have hm := functorIso_postcomp_heq_of_map_eq e hq.symm
  have ht : ((e.postcomp p).postcomp t).postcomp v = e.postcomp (p ≫ t ≫ v) := by
    rw [functorIso_postcomp_postcomp, functorIso_postcomp_postcomp]
  exact hm.trans (heq_of_eq ht).symm

end SerrePositivity.InfinityCategories.F2
