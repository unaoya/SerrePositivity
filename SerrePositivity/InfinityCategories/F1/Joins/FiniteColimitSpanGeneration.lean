module

public import SerrePositivity.InfinityCategories.F1.Joins.FiniteColimitGeneration
public import SerrePositivity.InfinityCategories.F1.Joins.PointConeSpanIso
public import SerrePositivity.InfinityCategories.F1.Joins.EmptyShapeExistence

/-!
概要：始対象と標準 span の余極限から、全有限余極限を生成する。
方針：空形状基底と三頂点 span の同型を、有限セル帰納へ渡す。
規約：押し出しは元の標準ホーン全図式の native な余極限として量化する。
使われ方：Ind と一般の quasicategory の有限余極限存在の公開判定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 始対象と全押し出しが存在すれば、全有限単体集合形状の余極限が存在する。 -/
lemma hasFiniteColimits_of_initial_pushouts {X : SSet.{u}} [Quasicategory X]
    (t : X _⦋0⦌) (ht : IsInitialVertex t)
    (hs : ∀ p : (horn 2 0 : SSet.{u}) ⟶ X, HasColimit p) : HasFiniteColimits X := by
  apply hasFiniteColimits_of_empty_pointSpan
    (fun T p => hasColimit_emptyDiagram_of_initial p t ht)
  intro p
  exact (F1B.kanHasColimit_iff_restrict_of_isIso p pointConeSpanIso.inv).mpr (hs _)

end SerrePositivity.InfinityCategories
