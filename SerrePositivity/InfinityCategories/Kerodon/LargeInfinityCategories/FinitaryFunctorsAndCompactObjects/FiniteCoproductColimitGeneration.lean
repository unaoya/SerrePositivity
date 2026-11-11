module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CountableStageKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CountableNerve
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialPreservedColimits

/-!
概要：小余積と全有限余極限の存在・保存から全小形状の保存余極限を構成する。
方針：有限段階の局所左 Kan と可算列で可算形状を閉じ、既存の実現版へ接続する。
規約：元の関手・元の図式を保持し、幾何学的実現版の証明を複製しない。
使われ方：P-11、HTT 4.4.2.6–7 の供給入口。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 概要：有限図式と可算列の保存余極限から可算形状の反転の保存余極限を得る。
方針：反対単体圏の段階関手に局所左 Kan 合成を適用し、局所化制限で戻す。
規約：元の可算列の保存を明示的な引数にする。
使われ方：小余積から得た可算列の保存の適用先。 -/
lemma hasPreservedColimit_countable_op_of_finite_sequential
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hfin : ∀ (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U D)
    (hseq : ∀ G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U G)
    (B : SSet.{u}) [Countable B.S]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B.op ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U F := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasPreservedColimit_iff_oppositeSimplexRestriction U B F).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasPreservedColimit_of_localLeftKan U
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B)))
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSimplexRestriction B) ≫ F)
  · rintro ⟨v⟩
    obtain ⟨n, rfl⟩ := nerveEquiv.symm.surjective v
    obtain ⟨n⟩ := n
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasPreservedColimit_countableStage_leftKan U hfin B F n
  · exact hseq

/-- 概要：小余積と有限余極限から任意の可算形状の保存余極限を得る。
方針：形状を反転し、有限段階と可算列を合成して二重反転を消す。
規約：形状の quasicategory 性は不要。使われ方：幾何学的実現の存在・保存。 -/
lemma hasPreservedColimit_countable_of_coproducts_finite
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallCoproducts U)
    (hfin : ∀ (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U D)
    (K : SSet.{u}) [Countable K.S]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U F := by
  have : Countable K.op.S := Countable.of_equiv K.S S.opEquiv.symm
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso (SSet.opFunctorCompOpFunctorIso.app K)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence e.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_iff_nativeRestriction F e.hom U
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre e.hom
      (he X).isFullyFaithful F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre e.hom
      (he Y).isFullyFaithful (F ≫ U))).mpr
  exact hasPreservedColimit_countable_op_of_finite_sequential U hfin
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasPreservedColimit_sequential_of_coproducts_finite U hX hU hfin) K.op (e.hom ≫ F)

/-- 概要：小余積と全有限余極限の存在・保存から全小形状の保存余極限を得る。
方針：可算形状の実現を構成し、P の既存の小余積・実現版を再利用する。
規約：追加のモデル圏仮定は不要で、元の図式そのものについて結論する。
使われ方：P-11、HTT 4.4.2.6–7 の最終入口。 -/
lemma hasPreservedColimit_of_coproducts_finite
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallCoproducts U)
    (hfin : ∀ (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U D)
    (K : SSet.{u}) (F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasPreservedColimit_of_coproducts_preservedRealizations U hX hU _ K F
  intro G
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countable_geometricRealizationShape_simplices.{u}
  exact hasPreservedColimit_countable_of_coproducts_finite U hX hU hfin _ G

/-- 概要：小余積と全有限余極限を保つ関手は元の全小余極限を保つ。
方針：構成した保存余極限から任意の指定余錐へ一意性で移す。
規約：元の指定余錐の像を結論する。使われ方：P-11 の保存判定としての公開入口。 -/
lemma preservesSmallColimits_of_coproducts_finite
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallCoproducts U)
    (hfin : ∀ (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U D) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits U := by
  intro K F c hc
  exact (hasPreservedColimit_of_coproducts_finite U hX hU hfin K F).map_isColimit c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
