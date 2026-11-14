module

public import SerrePositivity.KST.LocalizingInvariants.FinalHornArrowSquares
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColumnPushout
public import SerrePositivity.InfinityCategories.HA.Section6_1_1.SquareDuality

/-!
概要：矢印の恒等辺が表す実正方形は pullback である。
方針：正方形を反転・転置し、任意の quasicategory での列押し出しへ帰着する。
規約：安定性は使わない。使われ方：最終外ホーンの末尾頂点の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma identityArrowSquare_isPullback {X : SSet.{u}} [Quasicategory X]
    (f : (Δ[1] : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (fst (Δ[1] : SSet.{u}) Δ[1] ≫ f) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid _).mpr
  apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mpr
  have h : (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (fst Δ[1] Δ[1] ≫ f) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram ((stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map f) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨s, t⟩
    rfl
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram_isPushout _

lemma constantArrowFamily_isPullback {X : SSet.{u}} [Quasicategory X]
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (uncurry (SSet.const v : (Δ[1] : SSet.{u}) ⟶
      (ihom (Δ[1] : SSet.{u})).obj X)) := by
  obtain ⟨f, hf⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) X).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f = v at hf
  rw [← hf, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  exact identityArrowSquare_isPullback f

end SerrePositivity.KST.LocalizingInvariants
