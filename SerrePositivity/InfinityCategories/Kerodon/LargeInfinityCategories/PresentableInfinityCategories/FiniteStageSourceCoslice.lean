module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TerminalSourceCompactFactorization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.UniversePointCoslice
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredCosliceCofinality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary

/-!
概要：filtered 表示の全有限前置図式の下で、元の後続段への分裂比較を構成する。
方針：有限単体の下の添字を同じ小宇宙で使い、終頂点付き coslice の compact 因子化を適用する。
規約：元の有限前置図式と元の表示余錐を全て保持する。
使われ方：可算交互図式の coherent な有限段階の延長。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：元の有限前置図式を大きい標準単体から表示する。
方針：小さい標準単体の持ち上げ同型を介する。
規約：元の小さい添字の図式は変更しない。
使われ方：coslice の固定図式の宇宙整合。 -/
def finiteStageBaseMap {n : ℕ} {I : SSet.{u}} (a : (Δ[n] : SSet.{u}) ⟶ I) :
    (Δ[n] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj I :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} n).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map a

/-- 概要：有限前置図式の下の添字の宇宙比較は全 coslice の同型。
方針：一般の持ち上げ同型を標準単体の宇宙同型で制限する。
規約：固定図式を finiteStageBaseMap に揃える。
使われ方：小さい filtered 添字を元の標的の coslice へ送る。 -/
def finiteStageSourceCosliceIso {n : ℕ} {I : SSet.{u}}
    (a : (Δ[n] : SSet.{u}) ⟶ I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (finiteStageBaseMap a) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_isIso ((SSet.uliftFunctor.{u + 1, u}).map a)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} n).inv
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderIso a ≪≫ asIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict ((SSet.uliftFunctor.{u + 1, u}).map a) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).inv)

/-- 概要：全有限前置図式の宇宙同型は、元の終域射影を保つ。
方針：二つの同型の射影等式を合成する。
規約：全次数での厳密な関手等式。
使われ方：元の添字への cofinal 性の移送。 -/
lemma finiteStageSourceCosliceIso_projection {n : ℕ} {I : SSet.{u}}
    (a : (Δ[n] : SSet.{u}) ⟶ I) :
    (finiteStageSourceCosliceIso a).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (finiteStageBaseMap a) =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) := by
  dsimp only [finiteStageSourceCosliceIso, finiteStageBaseMap, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftSliceUnderIso_projection]

/-- 概要：compact な終段と頂点を持つ表示は、全有限前置図式を保って後続段で分裂する。
方針：有限前置図式の下の小さい filtered 添字を、同じ coslice の compact 因子化に渡す。
規約：元の前置図式の全高次と元の表示脚を保持する。
使われ方：全交互前置図式へ持ち上げる分裂三角形の供給。 -/
lemma finiteStage_compact_presentation_section
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I]
    {C : SSet.{u + 1}} [Quasicategory C] {n : ℕ}
    (a : (Δ[n] : SSet.{u}) ⟶ I)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((finiteStageBaseMap a ≫ D).app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex) :
    let s := (finiteStageSourceCosliceIso a).hom
    let F := s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (finiteStageBaseMap a) D
    let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone (finiteStageBaseMap a) s D c
    ∃ j : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌,
      ∃ t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (finiteStageBaseMap a ≫ D)).Edge v.vertex (F.app _ (ULift.up j)),
        Nonempty (t.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg v (ULift.up j))
          (SSet.Edge.id v.vertex)) := by
  let s := (finiteStageSourceCosliceIso a).hom
  have hreg : μ.IsRegular := Fact.out
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_sliceUnder hreg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hreg.aleph0_le _) a
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered hreg.aleph0_le I
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (finiteStageBaseMap a)) := by
    dsimp only [s]
    rw [finiteStageSourceCosliceIso_projection]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isRightCofinal_sliceUnderProjection_of_filtered a)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalSource_relative_presentation_section hμ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.stdSimplex_last_isTerminalVertex n)
    (finiteStageBaseMap a) s D c hc hs ha hv

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
