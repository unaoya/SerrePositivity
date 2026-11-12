module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.LiftedIntervalCospanRectification
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementSection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-!
概要：持ち上げた interval cospan の厳密化後の左成分の同値性。
方針：元の interval 射影の同値性を定値切断で検出し、同じ指定持ち上げで移す。
規約：置換の成分を別に選ばない。使われ方：元の interval 引き戻しと切断模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits SSet
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.F2

/-- 元の interval 置換の射影は、定値切断を逆に持つホモトピー同値。 -/
lemma intervalReplacementProjection_homotopyEquivalence
    {X Z : SSet.{u}} [KanComplex X] [KanComplex Z] (f : X ⟶ Z) :
    IsSimplicialHomotopyEquivalence
      (pullback.snd ((intervalEndpointNatTrans 0).app Z) f) := by
  have hw := intervalReplacementSection_isWeakHomotopyEquivalence f
  have hs := hw.isSimplicialHomotopyEquivalence
  apply hs.cancel_left
  rw [intervalReplacementSection_projection]
  exact HomotopyLimits.homotopyEquivalence_of_isIso (𝟙 X)

variable {X Z : SSet.{u}} [KanComplex X] [KanComplex Z]
  {E B : SSet.{max u v}} [KanComplex E] [KanComplex B]
  (f : X ⟶ Z) (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
  (s : (SSet.uliftFunctor.{v, u}).obj X ⟶ E)
  (t : (SSet.uliftFunctor.{v, u}).obj Z ⟶ B)
  (hs : (SSet.uliftFunctor.{v, u}).map f ≫ t = s ≫ p)

/-- 元の左成分が同値なら、全 path の持ち上げで厳密化した左成分も同値。 -/
lemma liftedIntervalCospanLeft_homotopyEquivalence
    (es : IsSimplicialHomotopyEquivalence s) :
    IsSimplicialHomotopyEquivalence (liftedIntervalCospanLeft f p s t hs) := by
  have : KanComplex (pullback ((intervalEndpointNatTrans 0).app Z) f) :=
    inferInstanceAs (KanComplex (intervalReplacement f))
  apply kanHomotopyRectification_homotopyEquivalence
  exact (intervalReplacementProjection_homotopyEquivalence f).ulift.comp es

end SerrePositivity.InfinityCategories.F2
