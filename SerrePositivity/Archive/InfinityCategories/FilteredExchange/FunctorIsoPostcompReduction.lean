module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoChainTransport

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoChainTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition

/-!
概要：二段の後合成が指定した同じ射に一致すれば、その指定像を型付きで簡約する。
方針：同じ三つの後合成の結合則と、元の合成射の明示した等式を使う。
規約：指定同型の像を保持。使われ方：定値切断と終点評価を元の外脚へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ指定二射の合成を元の射へ戻しても、その後の指定像は型付きで一致する。 -/
lemma functorIso_postcomp_pair_heq_of_comp_eq {A X Y Z W : SSet.{u}} {f g : A ⟶ X}
    (e : FunctorIso f g) (s : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z) (hs : s ≫ p = r)
    (w : Z ⟶ W) :
    HEq (((e.postcomp s).postcomp p).postcomp w) ((e.postcomp r).postcomp w) := by
  have h₀ : ((e.postcomp s).postcomp p).postcomp w = e.postcomp ((s ≫ p) ≫ w) := by
    rw [functorIso_postcomp_postcomp e s p, functorIso_postcomp_postcomp]
  have hm := functorIso_postcomp_heq_of_map_eq e
    (congrArg (fun k => k ≫ w) hs).symm
  have h₁ := functorIso_postcomp_postcomp e r w
  exact (heq_of_eq h₀).trans (hm.trans (heq_of_eq h₁.symm))

end SerrePositivity.InfinityCategories.F2
