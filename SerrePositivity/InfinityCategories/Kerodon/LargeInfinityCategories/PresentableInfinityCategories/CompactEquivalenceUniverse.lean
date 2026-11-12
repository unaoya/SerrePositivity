module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FullyFaithfulHomComparison
public import SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.EquivalenceColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.UniverseCoconePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentableRetractions

/-!
概要：κ-compact 性は、元の同値と同じ小さい κ-filtered 全余錐によって輸送できる。
方針：充満忠実関手の全 Hom 同型で反映し、逆同値と元の合成同型で保存も得る。
規約：元の全共変 Hom の定義と添字の宇宙を保持。compact 性を追加仮定に隠さない。
使われ方：κ-accessible 圏の compact 生成族の同値による輸送。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：小さい κ-filtered 余極限を保つ充満忠実関手は κ-compact 性を反映する。
方針：全共変 Hom 比較同型で、元の指定余錐の像を戻す。
規約：添字の宇宙 u と圏の宇宙 max u v を分離する。
使われ方：D-8 の同値・包含による compact 性の輸送。 -/
lemma isKappaCompact_of_fullyFaithful_image_universe {κ : Cardinal.{u}}
    {C E : SSet.{max u v}} [Quasicategory C] [Quasicategory E]
    (G : C ⟶ E) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G)
    (hp : ∀ (I : SSet.{u}) [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
      (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c))
    (x : C _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ (G.app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ x := by
  intro I hI hκ D c hc
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone
      ((SSet.uliftFunctor.{max u v + 1, max u v}).map G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (G.app (Opposite.op ⦋0⦌) x)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.mapJoinCocone_universe_comp]
    exact hx I (D ≫ G) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c) (hp I D c hc)
  exact h.of_functorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparisonIso G hG x).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c).val).symm

/-- 概要：元の同値は同じ対象の κ-compact 性を保存する。
方針：逆同値による反映と元の合成同型を使う。
規約：κ と試験添字の宇宙を変更しない。
使われ方：大きい圏の compact 対象の同値輸送。 -/
lemma isKappaCompact_image_of_equivalence_universe {κ : Cardinal.{u}}
    {C E : SSet.{max u v}} [Quasicategory C] [Quasicategory E]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) (x : C _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ (e.hom.app (Opposite.op ⦋0⦌) x) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso (κ := κ) (e.homInvIso.app x)).mpr hx
  exact isKappaCompact_of_fullyFaithful_image_universe e.inv
    e.symm.isQCatEquivalence.isFullyFaithful
    (fun _ _ _ _ c hc ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff e.symm.isQCatEquivalence c).mp hc) _ h

/-- 概要：元の同値は宇宙を分離した κ-compact 性を保存・反映する。
方針：同じ像の保存と充満忠実な同値による反映を結合する。
規約：元の対象と元の同値の像を保持する。
使われ方：D-8 の compact 性の同値不変性。 -/
lemma isKappaCompact_iff_equivalence_universe {κ : Cardinal.{u}}
    {C E : SSet.{max u v}} [Quasicategory C] [Quasicategory E]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ x ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ (e.hom.app (Opposite.op ⦋0⦌) x) :=
  ⟨isKappaCompact_image_of_equivalence_universe e x,
    isKappaCompact_of_fullyFaithful_image_universe e.hom e.isQCatEquivalence.isFullyFaithful
      (fun _ _ _ _ c hc ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff e.isQCatEquivalence c).mp hc) x⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
