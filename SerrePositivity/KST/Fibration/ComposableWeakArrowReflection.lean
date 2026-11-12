module
public import SerrePositivity.KST.Fibration.HornDiagramReflection
public import SerrePositivity.KST.Fibration.WeakArrowAmbientExact
public import SerrePositivity.KST.Fibration.WeakStringTwoHornComponents
public import SerrePositivity.KST.SConstruction.CofiberPreservesPushout

/-! # 接続した W 辺の両射影による S 構成の条件の反映

周囲の全ホーン図式で点ごとに普遍性を確認し、元の全部分図式圏へ反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 両 W 辺射影が零対象なら元の接続図式も零対象。 -/
lemma composableWeakArrow_isZeroVertex_of_components {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (v : (composableWeakArrowModel q).carrier _⦋0⦌)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((composableWeakFirstMap q).app (Opposite.op ⦋0⦌) v))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((composableWeakNextMap q).app (Opposite.op ⦋0⦌) v)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v := by
  have h₀' := (weakArrowInclusion_preservesCofiberData q).1 _ h₀
  have h₁' := (weakArrowInclusion_preservesCofiberData q).1 _ h₁
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((composableWeakFirstMap q ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι).app _ v) at h₀'
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((composableWeakNextMap q ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι).app _ v) at h₁'
  rw [composableWeakFirstMap_ι] at h₀'
  rw [composableWeakNextMap_ι] at h₁'
  have hz := innerTwoHorn_isZeroVertex_of_edges v.val h₀' h₁'
  exact ⟨isInitialVertex_fullSubcomplex_of_ambient _ v hz.1,
    isTerminalVertex_fullSubcomplex_of_ambient _ v hz.2⟩

/-- 両 W 辺射影が実押し出しを持つなら元の接続図式の正方形も押し出し。 -/
lemma composableWeakArrow_isPushoutSquare_of_components {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (composableWeakArrowModel q).carrier)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ composableWeakFirstMap q))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ composableWeakNextMap q)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F := by
  apply isPushoutSquare_fullSubcomplex_of_ambient (composableWeakArrowPredicate q).predicate
  apply innerTwoHorn_isPushoutSquare_of_edges
  · have h := (stableModelHom_preservesSConstructionData (weakArrowAmbientInclusion q)).2 _ h₀
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((F ≫ composableWeakFirstMap q) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι) at h
    rw [Category.assoc, composableWeakFirstMap_ι, ← Category.assoc] at h
    exact h
  · have h := (stableModelHom_preservesSConstructionData (weakArrowAmbientInclusion q)).2 _ h₁
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((F ≫ composableWeakNextMap q) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι) at h
    rw [Category.assoc, composableWeakNextMap_ι, ← Category.assoc] at h
    exact h

/-- 元の Ar 図式の gapped 条件は両短辺への射影から正確に判定できる。 -/
lemma composableWeakArrow_isGapped_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : ℕ} (F : arNerve n ⟶ (composableWeakArrowModel q).carrier) :
    IsGapped F ↔ IsGapped (F ≫ composableWeakFirstMap q) ∧
      IsGapped (F ≫ composableWeakNextMap q) := by
  constructor
  · intro h
    exact ⟨h.postcomp _ (stableModelHom_preservesSConstructionData (composableWeakFirstExact q)),
      h.postcomp _ (stableModelHom_preservesSConstructionData (composableWeakNextExact q))⟩
  · rintro ⟨h₀, h₁⟩
    constructor
    · intro i
      exact composableWeakArrow_isZeroVertex_of_components q _ (h₀.1 i) (h₁.1 i)
    · intro i j k l hij hjk hkl
      apply composableWeakArrow_isPushoutSquare_of_components q
      · simpa only [Category.assoc] using h₀.2 i j k l hij hjk hkl
      · simpa only [Category.assoc] using h₁.2 i j k l hij hjk hkl

end SerrePositivity.KST.Fibration
