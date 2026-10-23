module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionLimits
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionOppositeGeneral
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeReversePostcomp

/-!
概要：元の任意の冪等完備化は、元の図式に既に存在する全余極限余錐を保存する。
方針：元の全余錐を反転し、同じ元の反転関手の極限保存を適用する。
規約：有限性も inner 仮定も課さず、指定された元の余錐の像を保持する。
使われ方：HA 1.1.3.7 の既存の有限余極限と cofiber 四角形の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の任意の冪等完備化は、元の全図式の指定余極限余錐の同じ像を余極限へ送る。 -/
lemma IsIdempotentCompletion.mapJoinCocone_isColimit {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f)
    {p : K ⟶ C} (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone f c) := by
  have h := IsIdempotentCompletion.mapJoinCone_isLimit (SSet.opFunctor.map f)
    (IsIdempotentCompletion.op_general f hf) (F1B.kanCoconeReverseCone c)
    ((F1B.kanIsColimitCone_iff_reverseCone c).mp hc)
  exact (F2.isLimitCone_reverse_postcomp_iff c f).mp h

/-- 元の任意の冪等完備化は、元の図式の余極限の存在をその同じ像へ移す。 -/
lemma IsIdempotentCompletion.hasColimit_comp {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f)
    (p : K ⟶ C) (hp : HasColimit p) : HasColimit (p ≫ f) := by
  obtain ⟨c, hc⟩ := hp
  exact ⟨mapJoinCocone f c, IsIdempotentCompletion.mapJoinCocone_isColimit f hf c hc⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
