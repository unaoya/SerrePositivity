module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.CouplingsOfInfinityCategories.AdjunctionHomFamily
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ObjectCompactCardinals
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Preservation

/-!
概要：右随伴に沿う Hom 族の filtered 余極限保存を左随伴の像の compact 性で判定する。
方針：随伴の全自然な Hom 同型で保存性を移し、小さい族の共通濃度を選ぶ。
規約：右随伴そのものの accessibility はこの段階の仮定にも結論にも含めない。
使われ方：随伴関手定理の右随伴の accessibility の濃度調整。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：右随伴に沿う Hom の保存性は対応する左随伴の像の compact 性と同値。
方針：元の全 Hom 関手の随伴同型で両向きに保存性を移す。
規約：指定濃度を変更せず、全 coherent な filtered 添字を扱う。
使われ方：小さい生成対象族による右随伴の保存判定。 -/
lemma adjunction_hom_preservesKappaFilteredColimits_iff
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    (κ : Cardinal.{u}) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x) ↔
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (L.app (Opposite.op ⦋0⦌) x) := by
  constructor
  · intro h
    exact h.of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.CouplingsOfInfinityCategories.adjunctionCovariantHomIso a x).symm
  · intro h
    exact h.of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.CouplingsOfInfinityCategories.adjunctionCovariantHomIso a x)

/-- 概要：右随伴に沿う小さい Hom 族は共通の正則濃度の filtered 余極限を保つ。
方針：accessible な標的で左随伴の像の共通 compact 濃度を構成する。
規約：指定上限を超える濃度を選び、右随伴の保存性を仮定しない。
使われ方：生成対象の Hom 族による右随伴の accessibility の検証。 -/
lemma adjunction_exists_common_hom_preservationCardinal
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible D)
    {ι : Type u} (x : ι → C _⦋0⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ ∀ i,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ
        ((SSet.uliftFunctor.{u + 2, u + 1}).map R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (x i)) := by
  obtain ⟨μ, hμ, hσ, hx⟩ := hD.exists_common_compactCardinal
    (fun i ↦ L.app (Opposite.op ⦋0⦌) (x i)) σ
  exact ⟨μ, hμ, hσ, fun i ↦
    (adjunction_hom_preservesKappaFilteredColimits_iff a μ (x i)).mpr (hx i)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
