module
public import SerrePositivity.KST.NonConnective.DGKappaSplitCofiberEvaluations
public import SerrePositivity.KST.SConstruction.CofiberEvaluations
public import SerrePositivity.KST.SConstruction.FullSubcomplexGappedReflection

/-!
概要：元の全 cofiber 図式族を、同じ安定な Perf 入力の完全関手として束ねる。
方針：四角の元の dg 作用の完全性を全図式へ移し、全部分圏の内部へ反映する。
規約：D-12 の明示入力を保持し、一般 dg 加群の cofiber 判定は追加しない。
使われ方：同じ cone の連結 K で、元の三評価の加法性を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)
  (H : ∀ X : PresentedPerfectDGObject R (DGKappaCone R D I), DGKappaSplitCofiberInput R D I X)

private lemma action_preservesSData
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)) :
    PreservesSConstructionData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) F)) := by
  let := presentedPerfectDGNerve_isStable R (DGKappaCone R D I)
  let := presentedPerfectDGActionNerve_isExactFunctor R (DGKappaCone R D I) (DGKappaCone R D I) F
  exact ⟨fun x hx => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ hx,
    fun s hs => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare _ s hs⟩

/-- 元の全四角形族は、周囲の全関手圏で零対象と全押し出しを保つ。 -/
theorem dgKappaSplitCofiberFamily_ambient_preservesSData :
    PreservesSConstructionData (dgKappaSplitCofiberFamily R D I Z H ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) := by
  let := presentedPerfectDGNerve_isStable R (DGKappaCone R D I)
  apply preservesSConstructionData_functor_of_pointwise
  rintro ⟨a, b⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
  fin_cases i <;> fin_cases j
  · exact (congrArg (fun f => PreservesSConstructionData f)
      (dgKappaSplitCofiberFamily_subobject R D I Z H)).mpr (action_preservesSData R D I _)
  · exact (congrArg (fun f => PreservesSConstructionData f)
      (dgKappaSplitCofiberFamily_zero R D I Z H)).mpr (action_preservesSData R D I _)
  · exact (congrArg (fun f => PreservesSConstructionData f)
      (dgKappaSplitCofiberFamily_middle R D I Z H)).mpr (action_preservesSData R D I _)
  · exact (congrArg (fun f => PreservesSConstructionData f)
      (dgKappaSplitCofiberFamily_quotient R D I Z H)).mpr (action_preservesSData R D I _)

/-- 元の cofiber 図式族は、全部分圏の内部でも零対象と全押し出しを保つ。 -/
theorem dgKappaSplitCofiberFamily_preservesSData :
    PreservesSConstructionData (dgKappaSplitCofiberFamily R D I Z H) := by
  have ha := dgKappaSplitCofiberFamily_ambient_preservesSData R D I Z H
  constructor
  · intro x hx
    have hz := ha.1 x hx
    exact ⟨isInitialVertex_fullSubcomplex_of_ambient _ _ hz.1,
      isTerminalVertex_fullSubcomplex_of_ambient _ _ hz.2⟩
  · intro s hs
    apply isPushoutSquare_fullSubcomplex_of_ambient IsCofiberDiagramVertex
    simpa only [Category.assoc] using ha.2 s hs

/-- D-12 の明示入力の下で、元の全 cofiber 族を同じ安定 K 入力間の射にする。 -/
def dgKappaSplitCofiberStableMap :
    presentedPerfectDGStableModel R (DGKappaCone R D I) ⟶
      cofiberStableModel (presentedPerfectDGStableModel R (DGKappaCone R D I)) :=
  ⟨dgKappaSplitCofiberFamily R D I Z H,
    (dgKappaSplitCofiberFamily_preservesSData R D I Z H).toCofiberData⟩

end SerrePositivity.KST.NonConnective
