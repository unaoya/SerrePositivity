module

public import SerrePositivity.InfinityCategories.Core.FiniteShapeInduction
public import SerrePositivity.InfinityCategories.Core.FiniteLimitsColimits
public import SerrePositivity.InfinityCategories.F1.Joins.PushoutShapeColimit
public import SerrePositivity.InfinityCategories.F1.Joins.TerminalShapeColimit
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LimitColimitOpposite

/-!
概要：空形状と三頂点 span の余極限から全有限余極限を生成する。
方針：形状 pushout の余極限を構成し、全有限単体集合のセル帰納を適用する。
規約：有限性は元の単体集合について量化し、追加の交換仮定を要求しない。
使われ方：Ind の有限余極限存在と、一般の有限余極限の生成判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 空形状と三頂点 span の余極限が存在すれば、全有限形状の余極限が存在する。 -/
lemma hasFiniteColimits_of_empty_pointSpan {X : SSet.{u}} [Quasicategory X]
    (he : ∀ (T : SSet.{u}) (p : (⊥ : T.Subcomplex).toSSet ⟶ X), HasColimit p)
    (hs : ∀ p : pointConeSpan.{u} ⟶ X, HasColimit p) : HasFiniteColimits X := by
  constructor
  intro K _ p
  have h : ∀ q : K ⟶ X, HasColimit q :=
    finiteShape_induction_of_pushouts (fun A => ∀ q : A ⟶ X, HasColimit q)
      (fun e ih q => (F1B.kanHasColimit_iff_restrict_of_isIso q e.hom).mpr (ih _))
      he (fun n q => hasColimit_stdSimplex n q) (by
        intro A B C D f g i j _ hp hA hB hC q
        apply (F1B.kanHasColimit_iff_restrict_of_isIso q hp.isoPushout.inv).mpr
        exact hasColimit_pushout_shape_of_pointSpan f g (hp.isoPushout.inv ≫ q)
          (hA _) (hB _) (hC _) hs) K
  exact h p

end SerrePositivity.InfinityCategories
