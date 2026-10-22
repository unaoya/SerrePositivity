module

public import SerrePositivity.InfinityCategories.F2.Compact.Preservation
public import SerrePositivity.InfinityCategories.F2.Idempotent.RelativeInitialRetracts

/-!
概要：全余錐と κ-filtered 余極限保存関手は、全関手圏内の retract で閉じる。
方針：元の余錐制限の相対始点境界充填を retract へ戻す。
規約：全関手圏内の retract を使用し、成分ごとの分裂のみでは代用しない。
使われ方：共変 Hom 全関手の retract から κ-compact 対象の retract 閉性を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
open Idempotent

/-- 元の全余極限余錐の全関手圏内の retract は、その元の図式の余極限余錐。 -/
lemma isColimitCone_of_functorRetraction {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} {c : JoinCocone p} {d : JoinCocone q}
    (r : VertexRetraction (functorVertex c.val) (functorVertex d.val))
    (hd : IsColimitCone d) : IsColimitCone c := by
  apply isColimitCone_of_initialBoundaryLifting_coconeRestriction c
  exact initialBoundaryLifting_of_vertexRetraction (coconeRestriction K X) r
    hd.initialBoundaryLifting

/-- 全自然 retract で得た関手も、小さい κ-filtered 余極限を保存する。 -/
lemma PreservesKappaFilteredColimits.of_retract {κ : Cardinal.{u}}
    {C : SSet.{max u v}} {Y : SSet.{max u v + 1}} [Quasicategory Y]
    {F G : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶ Y}
    (r : VertexRetraction (functorVertex F) (functorVertex G))
    (hG : PreservesKappaFilteredColimits.{u, v} κ G) :
    PreservesKappaFilteredColimits.{u, v} κ F := by
  intro I hI hFiltered D c hc
  let c' := JoinCocone.ulift.{max u v, max u v + 1} c
  let q := (pre c'.val).app Y
  have hr : VertexRetraction (q.app (Opposite.op ⦋0⦌) (functorVertex F))
      (q.app (Opposite.op ⦋0⦌) (functorVertex G)) :=
    r.map (hoFunctor.map q).toFunctor
  change VertexRetraction (functorVertex (c'.val ≫ F))
    (functorVertex (c'.val ≫ G)) at hr
  exact isColimitCone_of_functorRetraction
    (c := mapJoinCocone F c') (d := mapJoinCocone G c') hr (hG I D c hc)

end SerrePositivity.InfinityCategories.F2.Compact
