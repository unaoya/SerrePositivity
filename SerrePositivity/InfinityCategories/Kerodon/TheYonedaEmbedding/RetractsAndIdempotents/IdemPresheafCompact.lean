module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.YonedaCompact
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Subcategory
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion

/-!
概要：元の Yoneda retract 閉包は、元の前層圏の κ-compact 対象の全部分圏へ入る。
方針：元の同じ retract と Yoneda 像の compact 性を使い、全包含を因子化する。
規約：元の Idem(C)・元の前層への包含・元の Yoneda を厳密に保持する。
使われ方：F2N-3(d) と F2N-4(e)、compact な Ind 対象との比較の準備。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の Idem(C) の各頂点の前層像は、同じ元の Yoneda retract として κ-compact。 -/
lemma idemPresheaf_isKappaCompact (κ : Cardinal.{u}) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusionPresheaf C).app _ F) := by
  obtain ⟨x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemVertex_retract_yoneda F
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_retract hx (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.yonedaInfinityMap_isKappaCompact κ x)

/-- 同じ元の Yoneda を、前層圏の元の κ-compact 全部分圏へ因子化する。 -/
def compactPresheafYoneda (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)
    (fun x ↦ by rcases x with ⟨x⟩; exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.yonedaInfinityMap_isKappaCompact κ x)

/-- compact 前層への因子化は、元の全 Yoneda 関手を厳密に回収する。 -/
lemma compactPresheafYoneda_inclusion (κ : Cardinal.{u}) :
    compactPresheafYoneda κ C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 元の Idem(C) の全包含を、同じ前層圏の元の κ-compact 全部分圏へ因子化する。 -/
def idemToCompactPresheaves (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusionPresheaf C)
    (idemPresheaf_isKappaCompact κ)

/-- 元の前層包含を同じ全写像として厳密に保持する。 -/
lemma idemToCompactPresheaves_inclusion (κ : Cardinal.{u}) :
    idemToCompactPresheaves κ C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusionPresheaf C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 元の Idem(C) から compact 前層への同じ実比較は充満忠実。 -/
lemma idemToCompactPresheaves_isFullyFaithful (κ : Cardinal.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (idemToCompactPresheaves κ C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion_isFullyFaithful.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)).cancel_right
  rw [idemToCompactPresheaves_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusionPresheaf_isFullyFaithful C

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
