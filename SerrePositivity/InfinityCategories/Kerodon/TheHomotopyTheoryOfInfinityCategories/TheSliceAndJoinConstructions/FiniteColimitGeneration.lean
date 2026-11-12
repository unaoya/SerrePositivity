module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapeInduction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FiniteLimitsColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShapeColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TerminalShapeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite

/-!
概要：空形状と三頂点 span の余極限から全有限余極限を生成する。
方針：形状 pushout の余極限を構成し、全有限単体集合のセル帰納を適用する。
規約：有限性は元の単体集合について量化し、追加の交換仮定を要求しない。
使われ方：Ind の有限余極限存在と、一般の有限余極限の生成判定。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 空形状と三頂点 span の余極限が存在すれば、全有限形状の余極限が存在する。 -/
lemma hasFiniteColimits_of_empty_pointSpan {X : SSet.{u}} [Quasicategory X]
    (he : ∀ (T : SSet.{u}) (p : (⊥ : T.Subcomplex).toSSet ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p)
    (hs : ∀ p : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpan.{u} ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X := by
  constructor
  intro K _ p
  have h : ∀ q : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit q :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.finiteShape_induction_of_pushouts (fun A => ∀ q : A ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit q)
      (fun e ih q => (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso q e.hom).mpr (ih _))
      he (fun n q => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasColimit_stdSimplex n q) (by
        intro A B C D f g i j _ hp hA hB hC q
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso q hp.isoPushout.inv).mpr
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasColimit_pushout_shape_of_pointSpan f g (hp.isoPushout.inv ≫ q)
          (hA _) (hB _) (hC _) hs) K
  exact h p

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
