module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.NativePreservationPosetReduction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseCoconeRestriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：宇宙分離版の小さい κ-filtered 余極限保存性を通常の κ-filtered poset 上の余錐へ帰着する。
方針：NativePreservationPosetReduction と同じ cofinal poset への制限を、持ち上げた余錐でも繰り返す。
規約：正則 κ と添字の宇宙 u を保ち、始域は max u v、標的は max u v + 1。元の余錐と関手を保持する。
使われ方：D-8 c2 の評価空間関手による native κ-filtered 余極限の保存。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 宇宙分離版：通常の小さい κ-filtered poset 上の全 coherent 余錐の持ち上げを保存すれば一般にも保存する。 -/
@[kerodon 06E0, kerodon 06E2]
lemma Compact.preservesKappaFilteredColimits_of_poset {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {C : SSet.{max u v}} {Y : SSet.{max u v + 1}} [Quasicategory C] [Quasicategory Y]
    (F : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶ Y)
    (h : ∀ (I : Type u) [PartialOrder I] [IsCardinalFiltered I κ]
      (D : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, v} κ F := by
  intro K hK hκ D c hc
  obtain ⟨I, o, f, hI, hN, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset (κ := κ) K
  let := o
  have : IsCardinalFiltered I κ := hI
  let f' := (SSet.uliftFunctor.{v, u}).map f
  have hf' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift f hf
  have hc' := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal f' hf' c).mp hc
  have hi := h I (f' ≫ D) (c.restrict f') hc'
  let f'' := (SSet.uliftFunctor.{max u v + 1, max u v}).map f'
  have hf'' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift f' hf'
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal f'' hf''
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c))).mpr
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mp hi
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift (c.restrict f')).val ≫ F =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f'' (𝟙 _) ≫ ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c).val ≫ F)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ulift_restrictJoinCocone_val, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
