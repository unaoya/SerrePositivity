module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialTelescopeSpineIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialTelescopeColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservedColimitGeneration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.InnerAnodyne
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FullyFaithfulPrecompositionColimits

/-!
概要：小余積と有限余極限の存在・保存から、元の可算列の保存余極限を構成する。
方針：望遠鏡上の余極限を作り、元の可算 nerve との全余錐比較で存在と保存を戻す。
規約：P の小余積の保存入口を読み取り専用で再利用し、主経路にモデル構造を要求しない。
使われ方：P-11 の幾何学的実現への有限骨格の可算合成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の可算列の保存余極限は小余積と有限余極限から構成できる。
方針：同じ列を望遠鏡へ制限して小余積・pushout で構成し、inner anodyne 比較で戻す。
規約：元の列とその元の関手による像の全余錐を同時に保持する。
使われ方：HTT 4.4.2.6 の可算列段階。 -/
lemma hasPreservedColimit_sequential_of_coproducts_finite
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallCoproducts U)
    (hfin : ∀ (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U D)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U F := by
  let r := (SSet.uliftFunctor.{u + 1, u}).map _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve.{u}
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence r :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne r
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.innerAnodyneExtensions_ulift_map _ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve_innerAnodyne)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_iff_nativeRestriction F r U
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre r
      (hr X).choose.isFullyFaithful F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre r
      (hr Y).choose.isFullyFaithful (F ≫ U))).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasPreservedColimit_sequentialTelescopeShape U
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasPreservedColimit_smallCoproduct U hX hU) hfin (r ≫ F)

/-- 概要：小余積・有限余極限を保つ関手は元の可算列の任意の指定余錐を保つ。
方針：構成した保存余極限から元の指定余錐へ一意性で移す。
規約：元の全余錐の像について結論する。
使われ方：幾何学的実現の骨格列の保存。 -/
lemma preservesSequentialColimits_of_coproducts_finite
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallCoproducts U)
    (hfin : ∀ (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U D)
    {F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone U c) :=
  (hasPreservedColimit_sequential_of_coproducts_finite U hX hU hfin F).map_isColimit c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
