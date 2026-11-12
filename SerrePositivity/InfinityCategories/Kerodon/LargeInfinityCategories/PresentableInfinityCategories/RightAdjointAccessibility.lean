module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndHomContinuityDetection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AdjunctionHomPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleIndRepresentation
public import SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.EquivalenceColimits
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalenceAdjunction

/-!
概要：accessible 圏の右随伴の accessibility を全 Hom 族の共通 compact 濃度で証明する。
方針：始域を Ind 模型へ移し、Yoneda Hom の保存を小さい評価族で検出する。
規約：指定宇宙変更の反映界面を明示入力として保持する。
使われ方：Compact の供給界面による随伴関手定理の必要条件の接続。

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

/-- 概要：accessible 圏の右随伴は、指定宇宙変更の反映界面の下で accessible。
方針：小さい生成 Hom 族を共通の正則濃度で保存し、Ind の各点検出で元の保存性へ戻す。
規約：右随伴の保存性や compact 性を追加入力にしない。
使われ方：無条件の宇宙反映界面を適用する随伴関手定理の必要方向。 -/
lemma rightAdjoint_isAccessible_of_spaceUniverseFullyFaithful
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram.{u})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible D)
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor R := by
  obtain ⟨κ, hκ⟩ := hC
  obtain ⟨A, hA, ⟨e⟩⟩ := hκ.exists_indEquivalence
  have := hA
  let a' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (e.hom ≫ L) (R ≫ e.inv) := e.toAdjunction.comp a
  obtain ⟨μ, hμ, _, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_exists_common_hom_preservationCardinal a' hD
    (fun x : A _⦋0⦌ ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up x)) κ
  have hR' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (R ≫ e.inv) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaAccessibleFunctor_of_indHomTests hU κ μ A (R ≫ e.inv) ht
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((R ≫ e.inv) ≫ e.hom) R := by
    simpa only [Category.assoc, Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.invHomIso R
  exact ⟨μ, hμ, (hR'.comp
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits μ e.isQCatEquivalence)).of_functorIso he⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
