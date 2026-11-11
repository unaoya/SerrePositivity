module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoproductRealizationPreservation

/-!
概要：有限余積と sifted 余極限の保存から全小余極限保存を導く。
方針：有限部分集合の filtered 余極限で小余積を作り、一般 bar 保存判定へ渡す。
規約：空の有限余積を含み、指定全余錐を保つ。
使われ方：P_Σ の全余極限保存判定の一般部。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects


/-- 概要：元の全有限余積を保つ条件。
方針：有限離散形状の元の指定全余錐の像を量化する。
規約：空添字を含む。
使われ方：全小余極限保存の有限条件。 -/
def PreservesFiniteCoproducts {X Y : SSet.{u + 1}} (U : X ⟶ Y) : Prop :=
  ∀ (I : Type u) [Finite I]
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone U c)

/-- 概要：有限余積と filtered 余極限の保存から小余積保存を得る。
方針：有限部分集合族の局所有限余積とその filtered 余極限を保存する。
規約：元の指定小余積余錐の像を結論に保持する。
使われ方：全小余極限保存判定の小余積段階。 -/
lemma preservesSmallCoproducts_of_finite_filtered
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X) (U : X ⟶ Y) (hfin : PreservesFiniteCoproducts U)
    (hfilter : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallCoproducts U := by
  intro I F c hc
  let Z := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetFamily I
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget I))
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget_nerve_isRightCofinal I)
  have hcq := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal q hq c).mp hc
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal q hq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone U c)).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.colimitPreservation_of_localLeftKan
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Z))) (q ≫ F) U
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproduct_leftKanDiagram_hasColimit Z hX _) ?_ ?_ (c.restrict q) hcq
  · intro v d hd
    rcases v with ⟨v⟩
    obtain ⟨s, rfl⟩ := nerveEquiv.symm.surjective v
    have : Finite (Z.obj s) := by
      change Finite {i // i ∈ s}
      infer_instance
    let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison Z s
    have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison_isRightCofinal Z s
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal a ha (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone U d)).mpr
    exact hfin _ _ (d.restrict a) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal a ha d).mp hd)
  · have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered Cardinal.aleph0 (nerve (Finset I)) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_aleph0_iff _).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubset_isFilteredInfinity I)
    exact hfilter _

/-- 概要：有限余積と sifted 余極限を保つ関手は全小余極限を保つ。
方針：小余積保存を有限部分集合で導き、幾何学的実現と合わせる。
規約：始域に小余積の存在だけを要求する。
使われ方：P_Σ の全余極限保存判定。 -/
lemma preservesSmallColimits_of_finiteCoproducts_sifted
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X) (U : X ⟶ Y) (hfin : PreservesFiniteCoproducts U)
    (hsift : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits U) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits U :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallColimits_of_coproducts_geometricRealizations hX U
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallCoproducts_of_finite_filtered hX U hfin
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallFiltered_of_sifted hsift)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallGeometric_of_sifted hsift)

/-- 概要：全小余極限保存は有限余積保存と sifted 保存に同値。
方針：十分条件と二種類の形状への制限を組み合わせる。
規約：始域の小余積存在を明示する。
使われ方：全小余極限保存の公開判定。 -/
lemma preservesSmallColimits_iff_finiteCoproducts_sifted
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X) (U : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits U ↔ PreservesFiniteCoproducts U ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits U :=
  ⟨fun h ↦ ⟨fun I _ p c hc ↦ h (nerve (Discrete I)) p c hc,
      fun I _ p c hc ↦ h I p c hc⟩,
    fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallColimits_of_finiteCoproducts_sifted hX U h.1 h.2⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
