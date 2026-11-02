module

public import SerrePositivity.InfinityCategories.Core.FilteredExchange.CoconeExistenceTransport
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.F1.Universe.EquivalenceDescent
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone

/-!
概要：小さい κ-filtered 模型と同値な大きい圏で、小さい試験形状の余錐を作る。
方針：逆比較で図式を降ろし、元の全余錐を持ち上げて関手同型で境界を戻す。
規約：元の試験図式を厳密に保持。使われ方：有限半順序図式表示の局所延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 小さい κ-small 試験図式の余錐は、実際の大きい同値先にも存在する。 -/
lemma nonempty_cocone_liftedShape_of_equivalence {κ : Cardinal.{u}}
    {I A : SSet.{u}} [Quasicategory I] [IsKappaFiltered κ I]
    {X : SSet.{u + 1}} [Quasicategory X]
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj I) X)
    (hA : IsKappaSmall κ A) (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ X) :
    Nonempty (JoinCocone q) := by
  let p := uliftMorphismDown (q ≫ e.inv)
  obtain ⟨c⟩ := IsKappaFiltered.cocone_nonempty hA p
  have hp : (SSet.uliftFunctor.{u + 1, u}).map p = q ≫ e.inv :=
    uliftMorphismDown_lift _
  have h : Nonempty (JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ e.hom)) :=
    ⟨mapJoinCocone e.hom (JoinCocone.ulift.{u, u + 1} c)⟩
  have he : FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map p ≫ e.hom) q := by
    rw [hp, Category.assoc]
    simpa only [Category.comp_id] using FunctorIso.precomp e.invHomIso q
  exact nonempty_joinCocone_of_functorIso he h

end SerrePositivity.InfinityCategories.F2.Ind
