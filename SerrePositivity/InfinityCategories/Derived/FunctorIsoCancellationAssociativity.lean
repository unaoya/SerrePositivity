module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerCancellation
/-!
概要：二つの中間同値を消去する順序の交換。
方針：指定済みの実射と比較同型の値を保持して照合する。
規約：生の dg 射の関手性や古い homInvIso の三角式は先取りしない。
使われ方：一般 cell 合成の五角式・単位三角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIsoCancellation_assoc {X E K Z : SSet.{u}} [Quasicategory K]
    (s : X ⟶ E) (B : E ⟶ K) (t : K ⟶ Z) (e : E ⟶ E) (k : K ⟶ K)
    (ε : FunctorIso e (𝟙 E)) (η : FunctorIso k (𝟙 K)) :
    ((ε.postcomp (B ≫ k ≫ t)).precomp s) ≪≫
        ((η.postcomp t).precomp (s ≫ B)) =
      ((η.postcomp t).precomp (s ≫ e ≫ B)) ≪≫
        ((ε.postcomp (B ≫ t)).precomp s) := by
  have h := F2.functorIso_whisker_exchange (ε.postcomp B) η
  have ht := congrArg (fun q => (FunctorIso.postcomp q t).precomp s) h
  simpa only [F2.functorIso_postcomp_trans, F2.functorIso_precomp_trans,
    F2.functorIso_postcomp_postcomp, F2.functorIso_precomp_postcomp,
    F2.functorIso_precomp_precomp, F2.functorIso_postcomp_id, Category.assoc] using! ht
end
end SerrePositivity.InfinityCategories
